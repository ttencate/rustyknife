use crate::bits::*;
use crate::bytes::Address;
use crate::errors::RuntimeError;
use crate::mem::{Memory, Version};
use crate::zstring::ZString;
use std::collections::BTreeSet;
use std::fmt;
use std::fmt::{Display, Formatter};

// 12.1
// The object table is held in dynamic memory and its byte address is stored in the word at $0a in
// the header.
pub struct ObjectTable<'a> {
    mem: &'a mut Memory,
}

impl<'a> ObjectTable<'a> {
    pub fn new(mem: &mut Memory) -> ObjectTable {
        ObjectTable { mem: mem }
    }

    // TODO add validation function, call it once when constructing the Memory

    pub fn get_name(&self, obj: Object) -> Result<String, RuntimeError> {
        let header_addr = self.obj_props_header_addr(obj)?;
        let text_length = self.mem.bytes().get_u8(header_addr)?;
        let text_addr = header_addr + 1;
        // This one is a bit special because 0-length zstrings are possible. So we construct it
        // from a slice directly, instead of scanning for a terminator word.
        let zstring = ZString::from(self.mem.bytes().get_slice(text_addr..text_addr + 2 * text_length)?);
        zstring.decode(self.mem.version(), &self.mem.abbrs_table())
    }

    pub fn get_parent(&self, obj: Object) -> Result<Object, RuntimeError> {
        obj.check_valid(self.mem.version())?;
        Ok(Object::from_number(self.mem.bytes().get_u8(self.parent_addr(obj))? as u16))
    }

    pub fn get_sibling(&self, obj: Object) -> Result<Object, RuntimeError> {
        obj.check_valid(self.mem.version())?;
        Ok(Object::from_number(self.mem.bytes().get_u8(self.sibling_addr(obj))? as u16))
    }

    pub fn get_child(&self, obj: Object) -> Result<Object, RuntimeError> {
        obj.check_valid(self.mem.version())?;
        Ok(Object::from_number(self.mem.bytes().get_u8(self.child_addr(obj))? as u16))
    }

    pub fn insert_obj(&mut self, obj: Object, dest: Object) -> Result<(), RuntimeError> {
        // Moves object O to become the first child of the destination object D. (Thus, after the
        // operation the child of D is O, and the sibling of O is whatever was previously the child
        // of D.) All children of O move with it. (Initially O can be at any point in the object
        // tree; it may legally have parent zero.)
        obj.check_valid(self.mem.version())?;
        dest.check_valid(self.mem.version())?;
        let prev_parent = self.get_parent(obj)?;
        if !prev_parent.is_null() {
            let mut prev_sibling = self.get_child(prev_parent)?;
            while !prev_sibling.is_null() {
                let next = self.get_sibling(prev_sibling)?;
                if next == obj {
                    self.set_sibling(prev_sibling, self.get_sibling(obj)?)?;
                    break;
                }
                prev_sibling = next;
            }
            if self.get_child(prev_parent)? == obj {
                self.set_child(prev_parent, self.get_sibling(obj)?)?;
            }
        }
        self.set_parent(obj, dest)?;
        self.set_sibling(obj, self.get_child(dest)?)?;
        self.set_child(dest, obj)?;
        Ok(())
    }

    pub fn get_attr(&self, obj: Object, attr: Attribute) -> Result<bool, RuntimeError> {
        obj.check_valid(self.mem.version())?;
        attr.check_valid(self.mem.version())?;
        let (addr, bit) = self.attr_addr(obj, attr)?;
        Ok(self.mem.bytes().get_u8(addr)?.bit(bit))
    }

    pub fn set_attr(&mut self, obj: Object, attr: Attribute, val: bool) -> Result<(), RuntimeError> {
        obj.check_valid(self.mem.version())?;
        attr.check_valid(self.mem.version())?;
        let (addr, bit) = self.attr_addr(obj, attr)?;
        let byte = self.mem.bytes().get_u8(addr)?.set_bit(bit, val);
        self.mem.bytes_mut().set_u8(addr, byte)
    }

    pub fn get_prop(&self, obj: Object, prop: Property) -> Result<u16, RuntimeError> {
        obj.check_valid(self.mem.version())?;
        prop.check_valid(self.mem.version())?;
        if let Some((prop_addr, prop_size)) = self.prop_addr(obj, prop)? {
            match prop_size {
                1 => Ok(self.mem.bytes().get_u8(prop_addr)? as u16),
                2 => Ok(self.mem.bytes().get_u16(prop_addr)?),
                _ => Err(RuntimeError::InvalidPropertySize(prop_size))
            }
        } else {
            // 12.2
            // ... When the game attempts to read the value of property n for an object which does
            // not provide property n, the n-th entry in this table is the resulting value.
            self.get_prop_default(prop)
        }
    }

    pub fn set_prop(&mut self, obj: Object, prop: Property, val: u16) -> Result<(), RuntimeError> {
        obj.check_valid(self.mem.version())?;
        prop.check_valid(self.mem.version())?;
        if let Some((prop_addr, prop_size)) = self.prop_addr(obj, prop)? {
            match prop_size {
                // TODO refactor so this goes through a writability check automatically
                1 => self.mem.bytes_mut().set_u8(prop_addr, val as u8)?,
                2 => self.mem.bytes_mut().set_u16(prop_addr, val)?,
                _ => return Err(RuntimeError::InvalidPropertySize(prop_size))
            };
            Ok(())
        } else {
            Err(RuntimeError::PropertyNotFound(obj, prop))
        }
    }

    pub fn guess_num_objects(&self) -> Result<usize, RuntimeError> {
        // The story file doesn't explictly store the number of objects. But Eric Lippert says: "In
        // practice, every story file has the property header for the properties of object 1
        // immediately following the last object entry. There is of course no requirement that the
        // property block for any object be anywhere, but this convention is consistently
        // followed."
        // https://ericlippert.com/2016/03/02/egyptian-room/
        let start = self.start_addr();
        let end = self.obj_props_addr(Object::from_number(1))?;
        Ok((end - start) / self.obj_size())
    }

    fn get_prop_default(&self, prop: Property) -> Result<u16, RuntimeError> {
        // 12.2
        // ... The ... property defaults table ... contains 31 words in Versions 1 to 3 and 63 in
        // Versions 4 and later. ...
        let addr = self.prop_defaults_addr() + 2 * prop.index();
        self.mem.bytes().get_u16(addr)
    }

    fn prop_defaults_addr(&self) -> Address {
        // 12.1
        // The object table is held in dynamic memory and its byte address is stored in the word at
        // $0a in the header. ...
        // 12.2
        // The table begins with a block known as the property defaults table.
        Address::from_byte_address(self.mem.bytes().get_u16(Address::from_byte_address(0x000a)).unwrap())
    }

    fn start_addr(&self) -> Address {
        match self.mem.version() {
            // 12.2
            // The table begins with a block known as the property defaults table. This contains 31
            // words in Versions 1 to 3 ...
            Version::V1 | Version::V2 | Version::V3 => self.prop_defaults_addr() + 31 * 2
            // ... and 63 in Versions 4 and later.
        }
    }

    fn obj_addr(&self, obj: Object) -> Address {
        self.start_addr() + obj.index() * self.obj_size()
    }

    fn attr_addr(&self, obj: Object, attr: Attribute) -> Result<(Address, Bit), RuntimeError> {
        // 12.3.1
        // ... Attributes 0 to 31 are flags (at any given time, they are either on (1) or off (0))
        // and are stored topmost bit first: e.g., attribute 0 is stored in bit 7 of the first
        // byte, attribute 31 is stored in bit 0 of the fourth.
        let (offset, bit) = attr.offset();
        Ok((self.obj_addr(obj) + offset, bit))
    }

    fn parent_addr(&self, obj: Object) -> Address {
        match self.mem.version() {
            Version::V1 | Version::V2 | Version::V3 => self.obj_addr(obj) + 4
        }
    }

    fn sibling_addr(&self, obj: Object) -> Address {
        match self.mem.version() {
            Version::V1 | Version::V2 | Version::V3 => self.obj_addr(obj) + 5
        }
    }

    fn child_addr(&self, obj: Object) -> Address {
        match self.mem.version() {
            Version::V1 | Version::V2 | Version::V3 => self.obj_addr(obj) + 6
        }
    }

    fn obj_props_header_addr(&self, obj: Object) -> Result<Address, RuntimeError> {
        let offset = match self.mem.version() {
            Version::V1 | Version::V2 | Version::V3 => 7
        };
        Ok(Address::from_byte_address(
            self.mem.bytes().get_u16(self.obj_addr(obj) + offset)
                .or(Err(RuntimeError::ObjectCorrupt(obj)))?))
    }

    fn obj_props_addr(&self, obj: Object) -> Result<Address, RuntimeError> {
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
        let header_addr = self.obj_props_header_addr(obj)?;
        let text_length = self.mem.bytes().get_u8(header_addr)
            .or(Err(RuntimeError::ObjectCorrupt(obj)))?;
        Ok(header_addr + 1 + 2 * text_length as usize * 2)
    }

    fn prop_addr(&self, obj: Object, prop: Property) -> Result<Option<(Address, u8)>, RuntimeError> {
        for res in PropertyIterator::new(self, obj, self.mem.version())? {
            let (p, addr, size) = res?;
            if p == prop {
                return Ok(Some((addr, size)));
            }
        }
        Ok(None)
    }

    fn obj_size(&self) -> usize {
        match self.mem.version() {
            Version::V1 | Version::V2 | Version::V3 => 9
        }
    }

    fn set_parent(&mut self, obj: Object, parent: Object) -> Result<(), RuntimeError> {
        match self.mem.version() {
            // TODO export V1 etc directly as well
            Version::V1 | Version::V2 | Version::V3 => {
                let addr = self.parent_addr(obj);
                self.mem.bytes_mut().set_u8(addr, parent.0 as u8)
            }
        }
    }

    fn set_sibling(&mut self, obj: Object, sibling: Object) -> Result<(), RuntimeError> {
        match self.mem.version() {
            Version::V1 | Version::V2 | Version::V3 => {
                let addr = self.sibling_addr(obj);
                self.mem.bytes_mut().set_u8(addr, sibling.0 as u8)
            }
        }
    }

    fn set_child(&mut self, obj: Object, child: Object) -> Result<(), RuntimeError> {
        match self.mem.version() {
            Version::V1 | Version::V2 | Version::V3 => {
                let addr = self.child_addr(obj);
                self.mem.bytes_mut().set_u8(addr, child.0 as u8)
            }
        }
    }

    // Useful for debugging.
    pub fn to_tree_string(&self) -> Result<String, RuntimeError> {
        let mut roots = BTreeSet::new();
        for i in 1..=self.guess_num_objects()? {
            let obj = Object::from_number(i as u16);
            if self.get_parent(obj)?.is_null() {
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
        out.push_str(&"      ".repeat(depth));
        out.push_str(&self.describe_object(obj)?);
        out.push('\n');
        let mut child = self.get_child(obj)?;
        while !child.is_null() {
            self.write_obj_tree(child, depth + 1, out)?;
            child = self.get_sibling(child)?;
        }
        Ok(())
    }

    fn describe_object(&self, obj: Object) -> Result<String, RuntimeError> {
        Ok(format!("[{:3}] {:30}  parent: [{:3}]  child: [{:3}]  sibling: [{:3}]",
                obj,
                self.get_name(obj)?,
                self.get_parent(obj)?,
                self.get_child(obj)?,
                self.get_sibling(obj)?))
    }
}

// 12.3
// ... Objects are numbered consecutively from 1 upward, with object number 0 being used to mean
// "nothing" (though there is formally no such object). ...
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Object(u16);

impl Object {
    pub fn from_number(num: u16) -> Object {
        Object(num)
    }

    pub fn number(self) -> u16 {
        self.0
    }

    fn index(self) -> usize {
        self.0 as usize - 1
    }

    fn is_null(self) -> bool {
        self.0 == 0
    }

    fn check_valid(self, version: Version) -> Result<(), RuntimeError> {
        if match version {
            // 12.3.1
            // In Versions 1 to 3, there are at most 255 objects...
            Version::V1 | Version::V2 | Version::V3 => self.0 >= 1 && self.0 <= 255
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
    pub fn from_number(num: u8) -> Property {
        Property(num as u8)
    }

    fn index(self) -> usize {
        self.0 as usize - 1
    }

    fn check_valid(self, version: Version) -> Result<(), RuntimeError> {
        if match version {
            // The maximum property number isn't explicitly written in the spec, but can be
            // inferred from the way the property table is stored.
            Version::V1 | Version::V2 | Version::V3 => self.0 >= 1 && self.0 <= 31
        } {
            Ok(())
        } else {
            Err(RuntimeError::InvalidProperty(self))
        }
    }
}

struct PropertyIterator<'a> {
    obj_table: &'a ObjectTable<'a>,
    version: Version,
    next_addr: Address,
}

impl<'a> PropertyIterator<'a> {
    fn new(obj_table: &'a ObjectTable<'a>, obj: Object, version: Version) -> Result<PropertyIterator<'a>, RuntimeError> {
        Ok(PropertyIterator {
            obj_table: obj_table,
            version: version,
            next_addr: obj_table.obj_props_addr(obj)?,
        })
    }
}

impl<'a> Iterator for PropertyIterator<'a> {

    type Item = Result<(Property, Address, u8), RuntimeError>;

    fn next(&mut self) -> Option<Self::Item> {
        // In Versions 1 to 3, each property is stored as a block
        //
        //    size byte     the actual property data
        //                 ---between 1 and 8 bytes--
        //
        // where the size byte is arranged as 32 times the number of data bytes minus one, plus the
        // property number. A property list is terminated by a size byte of 0. (It is otherwise
        // illegal for a size byte to be a multiple of 32.)
        match self.version {
            Version::V1 | Version::V2 | Version::V3 => {
                match self.obj_table.mem.bytes().get_u8(self.next_addr) {
                    Ok(size_byte) => {
                        if size_byte == 0 {
                            return None;
                        }
                        let prop_num = size_byte.bits(BIT0..=BIT4);
                        let prop = Property::from_number(prop_num);
                        let size = size_byte.bits(BIT5..=BIT7) + 1;
                        let item = Ok((prop, self.next_addr + 1, size));
                        self.next_addr += 1 + size;
                        Some(item)
                    }
                    Err(err) => {
                        Some(Err(err))
                    }
                }
            }
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
            Version::V1 | Version::V2 | Version::V3 => self.0 <= 31
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

impl<'a> Display for ObjectTable<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self.guess_num_objects() {
            Ok(n) => {
                for i in 1..=(n as u16) {
                    let obj = Object::from_number(i);
                    writeln!(f, "{}", self.describe_object(obj).unwrap_or_else(|e| e.to_string()))?;
                }
                Ok(())
            }
            Err(err) => writeln!(f, "{}", err)
        }
    }
}
