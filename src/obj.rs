use crate::bits::*;
use crate::bytes::{Address, Bytes};
use crate::errors::{FormatError, RuntimeError};
use crate::version::*;
use crate::zstring::{AbbreviationsTable, ZString};
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::rc::Rc;

// 12.1
// The object table is held in dynamic memory and its byte address is stored in the word at $0a in
// the header.
pub struct ObjectTable {
    version: Version,
    bytes: Rc<RefCell<Bytes>>,
    prop_defaults_addr: Address,
    start_addr: Address,
    abbrs_table: AbbreviationsTable,
}

impl ObjectTable {
    pub fn new(version: Version, bytes: Rc<RefCell<Bytes>>, base_addr: Address, abbrs_table: AbbreviationsTable) -> Result<ObjectTable, FormatError> {
        bytes.borrow().get_u16(base_addr).or(Err(FormatError::ObjectsTableOutOfRange(base_addr)))?;
        let start_addr = match version {
            // 12.2
            // The table begins with a block known as the property defaults table. This contains 31
            // words in Versions 1 to 3 ...
            V1 | V2 | V3 => base_addr + 31 * 2
            // ... and 63 in Versions 4 and later.
        };
        bytes.borrow().get_u16(start_addr).or(Err(FormatError::ObjectsTableOutOfRange(start_addr)))?;
        Ok(ObjectTable {
            version: version,
            bytes: bytes,
            prop_defaults_addr: base_addr,
            start_addr: start_addr,
            abbrs_table: abbrs_table,
        })
    }

    pub fn get_obj_ref(&self, obj: Object) -> Result<Option<ObjectRef>, RuntimeError> {
        Ok(if obj.is_null() {
            None
        } else {
            Some(ObjectRef::new(self.version, self.bytes.clone(), self.abbrs_table.clone(), obj, self.start_addr)?)
        })
    }

    pub fn guess_num_objects(&self) -> Result<usize, RuntimeError> {
        // The story file doesn't explictly store the number of objects. But Eric Lippert says: "In
        // practice, every story file has the property header for the properties of object 1
        // immediately following the last object entry. There is of course no requirement that the
        // property block for any object be anywhere, but this convention is consistently
        // followed."
        // https://ericlippert.com/2016/03/02/egyptian-room/
        let end = self.get_obj_ref(Object::from_number(1))?.unwrap().props_addr()?;
        Ok((end - self.start_addr) / obj_size(self.version))
    }

    // This method breaks abstraction, but we have no choice: the get_prop_addr instruction only
    // takes a property data addres as operand.
    pub fn get_prop_len(&self, prop_data_addr: Address) -> Result<u8, RuntimeError> {
        let offset = match self.version {
            V1 | V2 | V3 => -1,
        };
        Ok(PropertyRef::new(self.version, self.bytes.clone(), prop_data_addr + offset)?
            .ok_or(RuntimeError::InvalidPropertyAddress(prop_data_addr))?
            .len())
    }

    pub fn get_prop_default(&self, prop: Property) -> Result<u16, RuntimeError> {
        // 12.1
        // The object table is held in dynamic memory and its byte address is stored in the word at
        // $0a in the header. ...
        // 12.2
        // ... The ... property defaults table ... contains 31 words in Versions 1 to 3 and 63 in
        // Versions 4 and later. ...
        let addr = self.prop_defaults_addr + 2 * prop.index();
        self.bytes.borrow().get_u16(addr)
    }

    // Useful for debugging.
    pub fn to_tree_string(&self) -> Result<String, RuntimeError> {
        let mut roots = BTreeSet::new();
        for i in 1..=self.guess_num_objects()? {
            let obj = Object::from_number(i as u16);
            if self.get_obj_ref(obj)?.unwrap().parent()?.is_null() {
                roots.insert(obj);
            }
        }

        let mut out = String::new();
        out.push_str(&format!("{:?}", roots));
        for root in roots {
            self.write_obj_tree(root, 0, &mut out)?;
        }
        Ok(out)
    }

    fn write_obj_tree(&self, obj: Object, depth: usize, out: &mut String) -> Result<(), RuntimeError> {
        let obj_ref = self.get_obj_ref(obj)?.unwrap();
        out.push_str(&"      ".repeat(depth));
        out.push_str(&obj_ref.to_string());
        out.push('\n');
        let mut child = obj_ref.child()?;
        while !child.is_null() {
            self.write_obj_tree(child, depth + 1, out)?;
            child = self.get_obj_ref(child)?.unwrap().sibling()?;
        }
        Ok(())
    }
}

fn obj_size(version: Version) -> usize {
    match version {
        V1 | V2 | V3 => 9
    }
}

// 12.3
// ... Objects are numbered consecutively from 1 upward, with object number 0 being used to mean
// "nothing" (though there is formally no such object). ...
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Object(u16);

impl Object {
    pub fn null() -> Object {
        Object(0)
    }

    pub fn from_number(num: u16) -> Object {
        Object(num)
    }

    pub fn number(self) -> u16 {
        self.0
    }

    pub fn is_null(self) -> bool {
        self.0 == 0
    }

    fn index(self) -> usize {
        self.0 as usize - 1
    }

    fn check_valid(self, version: Version) -> Result<(), RuntimeError> {
        if match version {
            // 12.3.1
            // In Versions 1 to 3, there are at most 255 objects...
            V1 | V2 | V3 => self.0 >= 1 && self.0 <= 255
        } {
            Ok(())
        } else {
            Err(RuntimeError::InvalidObject(self))
        }
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:3}", self.0)
    }
}

// 12.1
// ... (Recall that objects have ... variables attached called properties, numbered from 1 upward.
// ...)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Property(u8);

impl Property {
    pub fn null() -> Property {
        Property(0)
    }

    pub fn from_number(num: u8) -> Property {
        Property(num as u8)
    }

    pub fn to_number(self) -> u8 {
        self.0
    }

    pub fn is_null(self) -> bool {
        self.0 == 0
    }

    fn index(self) -> usize {
        self.0 as usize - 1
    }

    fn check_valid(self, version: Version) -> Result<(), RuntimeError> {
        if match version {
            // The maximum property number isn't explicitly written in the spec, but can be
            // inferred from the way the property table is stored.
            V1 | V2 | V3 => self.0 >= 1 && self.0 <= 31
        } {
            Ok(())
        } else {
            Err(RuntimeError::InvalidProperty(self))
        }
    }
}

impl Display for Property {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone)]
pub struct ObjectRef {
    version: Version,
    bytes: Rc<RefCell<Bytes>>,
    abbrs_table: AbbreviationsTable,
    obj: Object,
    base_addr: Address,
    addr: Address,
}

impl ObjectRef {
    fn new(version: Version, bytes: Rc<RefCell<Bytes>>, abbrs_table: AbbreviationsTable, obj: Object, base_addr: Address) -> Result<ObjectRef, RuntimeError> {
        obj.check_valid(version)?;
        let addr = base_addr + obj.index() * obj_size(version);
        Ok(ObjectRef {
            version: version,
            bytes: bytes,
            abbrs_table: abbrs_table,
            obj: obj,
            base_addr: base_addr,
            addr: addr,
        })
    }

    pub fn name(&self) -> Result<String, RuntimeError> {
        let header_addr = self.props_header_addr()?;
        let text_length = self.bytes.borrow().get_u8(header_addr)?;
        let text_addr = header_addr + 1;
        // This one is a bit special because 0-length zstrings are possible. So we construct it
        // from a slice directly, instead of scanning for a terminator word.
        let zstring = ZString::from(self.bytes.borrow().get_slice(text_addr..text_addr + 2 * text_length as usize)?);
        zstring.decode(self.version, Some(&self.abbrs_table))
    }

    pub fn parent(&self) -> Result<Object, RuntimeError> {
        Ok(Object::from_number(self.bytes.borrow().get_u8(self.parent_addr())? as u16))
    }

    pub fn sibling(&self) -> Result<Object, RuntimeError> {
        Ok(Object::from_number(self.bytes.borrow().get_u8(self.sibling_addr())? as u16))
    }

    pub fn child(&self) -> Result<Object, RuntimeError> {
        Ok(Object::from_number(self.bytes.borrow().get_u8(self.child_addr())? as u16))
    }

    pub fn insert_into(&mut self, dest: Object) -> Result<(), RuntimeError> {
        // Moves object O to become the first child of the destination object D. (Thus, after the
        // operation the child of D is O, and the sibling of O is whatever was previously the child
        // of D.) All children of O move with it. (Initially O can be at any point in the object
        // tree; it may legally have parent zero.)
        dest.check_valid(self.version)?;

        self.remove_from_parent()?;

        if dest.is_null() {
            return Ok(())
        }

        let mut dest_ref = ObjectRef::new(self.version, self.bytes.clone(), self.abbrs_table.clone(), dest, self.base_addr)?;
        self.set_parent(dest)?;
        self.set_sibling(dest_ref.child()?)?;
        dest_ref.set_child(self.obj)?;
        Ok(())
    }

    pub fn remove_from_parent(&mut self) -> Result<(), RuntimeError> {
        // Detach the object from its parent, so that it no longer has any parent. (Its children
        // remain in its possession.)
        let parent = self.parent()?;
        if !parent.is_null() {
            let mut parent_ref = ObjectRef::new(self.version, self.bytes.clone(), self.abbrs_table.clone(), parent, self.base_addr)?;
            let mut prev_sibling = parent_ref.child()?;
            while !prev_sibling.is_null() {
                let mut prev_sibling_ref = ObjectRef::new(self.version, self.bytes.clone(), self.abbrs_table.clone(), prev_sibling, self.base_addr)?;
                let next = prev_sibling_ref.sibling()?;
                if next == self.obj {
                    prev_sibling_ref.set_sibling(self.sibling()?)?;
                    break;
                }
                prev_sibling = next;
            }
            if parent_ref.child()? == self.obj {
                parent_ref.set_child(self.sibling()?)?;
            }
            self.set_parent(Object::null())?;
        }
        Ok(())
    }

    pub fn attr(&self, attr: Attribute) -> Result<bool, RuntimeError> {
        attr.check_valid(self.version)?;
        let (addr, bit) = self.attr_addr(attr)?;
        Ok(self.bytes.borrow().get_u8(addr)?.bit(bit))
    }

    pub fn set_attr(&mut self, attr: Attribute, val: bool) -> Result<(), RuntimeError> {
        attr.check_valid(self.version)?;
        let (addr, bit) = self.attr_addr(attr)?;
        let byte = self.bytes.borrow().get_u8(addr)?.set_bit(bit, val);
        self.bytes.borrow_mut().set_u8(addr, byte)
    }

    pub fn get_prop_ref(&self, prop: Property) -> Result<Option<PropertyRef>, RuntimeError> {
        prop.check_valid(self.version)?;
        for res in self.iter_props()? {
            let prop_ref = res?;
            if prop_ref.prop == prop {
                return Ok(Some(prop_ref))
            }
        }
        Ok(None)
    }

    pub fn iter_props(&self) -> Result<PropertyIterator, RuntimeError> {
        PropertyIterator::new(self.version, self.bytes.clone(), Some(self.props_addr()?))
    }

    fn attr_addr(&self, attr: Attribute) -> Result<(Address, Bit), RuntimeError> {
        // 12.3.1
        // ... Attributes 0 to 31 are flags (at any given time, they are either on (1) or off (0))
        // and are stored topmost bit first: e.g., attribute 0 is stored in bit 7 of the first
        // byte, attribute 31 is stored in bit 0 of the fourth.
        let (offset, bit) = attr.offset();
        Ok((self.addr + offset, bit))
    }

    fn parent_addr(&self) -> Address {
        match self.version {
            V1 | V2 | V3 => self.addr + 4
        }
    }

    fn sibling_addr(&self) -> Address {
        match self.version {
            V1 | V2 | V3 => self.addr + 5
        }
    }

    fn child_addr(&self) -> Address {
        match self.version {
            V1 | V2 | V3 => self.addr + 6
        }
    }

    fn props_header_addr(&self) -> Result<Address, RuntimeError> {
        let offset = match self.version {
            V1 | V2 | V3 => 7
        };
        Ok(Address::from_byte_address(
            self.bytes.borrow().get_u16(self.addr + offset)
                .or(Err(RuntimeError::ObjectCorrupt(self.obj)))?))
    }

    fn props_addr(&self) -> Result<Address, RuntimeError> {
        // 12.4
        // Each object has its own property table. Each of these can be anywhere in dynamic memory
        // (indeed, a game can legally change an object's properties table address in play,
        // provided the new address points to another valid properties table). The header of a
        // property table is as follows:
        //
        //    text-length     text of short name of object
        //   -----byte----   --some even number of bytes---
        //
        // where the text-length is the number of 2-byte words making up the text, which is stored
        // in the usual format. 
        let header_addr = self.props_header_addr()?;
        let text_length = self.bytes.borrow().get_u8(header_addr)
            .or(Err(RuntimeError::ObjectCorrupt(self.obj)))?;
        Ok(header_addr + 1 + text_length as usize * 2)
    }

    fn set_parent(&mut self, parent: Object) -> Result<(), RuntimeError> {
        match self.version {
            V1 | V2 | V3 => {
                let addr = self.parent_addr();
                self.bytes.borrow_mut().set_u8(addr, parent.0 as u8)
            }
        }
    }

    fn set_sibling(&mut self, sibling: Object) -> Result<(), RuntimeError> {
        match self.version {
            V1 | V2 | V3 => {
                let addr = self.sibling_addr();
                self.bytes.borrow_mut().set_u8(addr, sibling.0 as u8)
            }
        }
    }

    fn set_child(&mut self, child: Object) -> Result<(), RuntimeError> {
        match self.version {
            V1 | V2 | V3 => {
                let addr = self.child_addr();
                self.bytes.borrow_mut().set_u8(addr, child.0 as u8)
            }
        }
    }
}

impl Display for ObjectRef {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "[{:3}] {:30}  parent: [{:3}]  child: [{:3}]  sibling: [{:3}]  {{",
                self.obj,
                self.name().unwrap_or_else(|e| e.to_string()),
                self.parent().map(|o| o.to_string()).unwrap_or_else(|e| e.to_string()),
                self.child().map(|o| o.to_string()).unwrap_or_else(|e| e.to_string()),
                self.sibling().map(|o| o.to_string()).unwrap_or_else(|e| e.to_string()))?;
        if let Ok(iter) = self.iter_props() {
            let mut first = true;
            for prop_ref in iter {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "{}", prop_ref.map(|p| p.to_string()).unwrap_or_else(|e| e.to_string()))?;
                first = false;
            }
        } else {
            write!(f, "<error getting props>")?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct PropertyRef {
    version: Version,
    bytes: Rc<RefCell<Bytes>>,
    prop: Property,
    data_addr: Address,
    len: u8,
}

impl PropertyRef {
    fn new(version: Version, bytes: Rc<RefCell<Bytes>>, size_byte_addr: Address) -> Result<Option<PropertyRef>, RuntimeError> {
        // In Versions 1 to 3, each property is stored as a block
        //
        //    size byte     the actual property data
        //                 ---between 1 and 8 bytes--
        //
        // where the size byte is arranged as 32 times the number of data bytes minus one, plus the
        // property number. A property list is terminated by a size byte of 0. (It is otherwise
        // illegal for a size byte to be a multiple of 32.)
        match version {
            V1 | V2 | V3 => {
                let size_byte = bytes.borrow().get_u8(size_byte_addr)?;
                if size_byte == 0 {
                    Ok(None)
                } else {
                    let prop_num = size_byte.bits(BIT0..=BIT4);
                    let len = size_byte.bits(BIT5..=BIT7) + 1;
                    let prop = Property::from_number(prop_num);
                    Ok(Some(PropertyRef {
                        version: version,
                        bytes: bytes,
                        prop: prop,
                        data_addr: size_byte_addr + 1,
                        len: len,
                    }))
                }
            }
        }
    }

    pub fn prop(&self) -> Property {
        self.prop
    }

    pub fn addr(&self) -> Address {
        self.data_addr
    }

    pub fn len(&self) -> u8 {
        self.len
    }

    pub fn get(&self) -> Result<u16, RuntimeError> {
        match self.len {
            1 => Ok(self.bytes.borrow().get_u8(self.data_addr)? as u16),
            2 => Ok(self.bytes.borrow().get_u16(self.data_addr)?),
            _ => Err(RuntimeError::InvalidPropertySize(self.len))
        }
    }

    pub fn set(&mut self, val: u16) -> Result<(), RuntimeError> {
        match self.len {
            // TODO refactor so this goes through a writability check automatically
            1 => self.bytes.borrow_mut().set_u8(self.data_addr, val as u8),
            2 => self.bytes.borrow_mut().set_u16(self.data_addr, val),
            _ => Err(RuntimeError::InvalidPropertySize(self.len)),
        }
    }
}

impl Display for PropertyRef {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}: ", self.prop)?;
        let bytes = self.bytes.borrow();
        let slice = bytes.get_slice(self.data_addr..(self.data_addr + self.len as usize));
        match slice {
            Ok(slice) => write!(f, "{:?}", slice),
            Err(err) => write!(f, "{}", err),
        }
    }
}

pub struct PropertyIterator {
    version: Version,
    bytes: Rc<RefCell<Bytes>>,
    next_addr: Option<Address>,
}

impl PropertyIterator {
    fn new(version: Version, bytes: Rc<RefCell<Bytes>>, props_addr: Option<Address>) -> Result<PropertyIterator, RuntimeError> {
        Ok(PropertyIterator {
            version: version,
            bytes: bytes,
            next_addr: props_addr,
        })
    }
}

impl Iterator for PropertyIterator {
    type Item = Result<PropertyRef, RuntimeError>;
    fn next(&mut self) -> Option<Result<PropertyRef, RuntimeError>> {
        if let Some(next_addr) = self.next_addr {
            match PropertyRef::new(self.version, self.bytes.clone(), next_addr) {
                Ok(prop_ref) => {
                    if let Some(prop_ref) = prop_ref {
                        self.next_addr = Some(prop_ref.data_addr + prop_ref.len as usize);
                        Some(Ok(prop_ref))
                    } else {
                        None
                    }
                }
                Err(err) => Some(Err(err))
            }
        } else {
            None
        }
    }
}

// 12.1
// ... (Recall that objects have flags attached called attributes, numbered from 0 upward, ...)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Attribute(u8);

impl Attribute {
    pub fn from_number(num: u8) -> Attribute {
        Attribute(num)
    }

    fn check_valid(self, version: Version) -> Result<(), RuntimeError> {
        if match version {
            // The maximum property number isn't explicitly written in the spec, but can be
            // inferred from the way the property table is stored.
            V1 | V2 | V3 => self.0 <= 31
        } {
            Ok(())
        } else {
            Err(RuntimeError::InvalidAttribute(self))
        }
    }

    fn offset(self) -> (usize, Bit) {
        // 12.3.1
        // ... Attributes 0 to 31 are flags (at any given time, they are either on (1) or off (0))
        // and are stored topmost bit first: e.g., attribute 0 is stored in bit 7 of the first
        // byte, attribute 31 is stored in bit 0 of the fourth.
        let idx = self.0 as usize;
        (idx / 8, Bit::number((7 - idx % 8) as u8))
    }
}

impl Display for ObjectTable {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self.guess_num_objects() {
            Ok(n) => {
                for i in 1..=(n as u16) {
                    let obj = Object::from_number(i);
                    writeln!(f, "{}", self.get_obj_ref(obj).map(|obj| obj.unwrap().to_string()).unwrap_or_else(|e| e.to_string()))?;
                }
                Ok(())
            }
            Err(err) => writeln!(f, "{}", err)
        }
    }
}
