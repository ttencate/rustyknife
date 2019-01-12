use crate::bytes::Bytes;
use crate::dict::DictionaryTable;
use crate::errors::FormatError;
use crate::globals::GlobalsTable;
use crate::header::Header;
use crate::obj::ObjectTable;
use crate::version::Version;
use crate::zstring::AbbreviationsTable;
use std::cell::{Ref, RefCell, RefMut};
use std::rc::Rc;

pub struct Memory {
    version: Version,
    // This needs to be Rc so that all "views" on it can hold references to it (which would
    // otherwise be forbidden because struct fields can't hold references to other fields in the
    // same struct). And of course, it needs to be RefCell to provide mutability.
    // TODO see if we can make Memory hold the Vec<u8> directly, as well as the cached fields, and
    // implement all the tables as traits on Memory instead. That could get rid of the unsafety.
    bytes: Rc<RefCell<Bytes>>,
    header: Header,
    globals_table: GlobalsTable,
    obj_table: ObjectTable,
    abbrs_table: AbbreviationsTable,
    dict_table: DictionaryTable,
}

impl Memory {
    pub fn wrap(bytes: Bytes) -> Result<Memory, FormatError> {
        let bytes = Rc::new(RefCell::new(bytes));
        let header = Header::new(bytes.clone())?;
        let version = header.version();
        let globals_table = GlobalsTable::new(version, bytes.clone(), header.globals_table_addr())?;
        let abbrs_table = AbbreviationsTable::new(version, bytes.clone(), header.abbrs_table_addr())?;
        let obj_table = ObjectTable::new(version, bytes.clone(), header.obj_table_addr(), abbrs_table.clone())?;
        let dict_table = DictionaryTable::new(version, bytes.clone(), header.dict_table_addr())?;

        Ok(Memory {
            version: version,
            bytes: bytes,
            header: header,
            globals_table: globals_table,
            abbrs_table: abbrs_table,
            obj_table: obj_table,
            dict_table: dict_table,
        })
    }

    pub fn version(&self) -> Version {
        self.version
    }

    pub fn bytes(&self) -> Ref<Bytes> {
        self.bytes.borrow()
    }

    pub fn bytes_mut(&mut self) -> RefMut<Bytes> {
        self.bytes.borrow_mut()
    }

    pub fn header(&self) -> &Header {
        &self.header
    }

    pub fn header_mut(&mut self) -> &mut Header {
        &mut self.header
    }

    pub fn globals(&self) -> &GlobalsTable {
        &self.globals_table
    }

    pub fn globals_mut(&mut self) -> &mut GlobalsTable {
        &mut self.globals_table
    }

    pub fn abbrs_table(&self) -> &AbbreviationsTable {
        &self.abbrs_table
    }

    pub fn obj_table(&self) -> &ObjectTable {
        &self.obj_table
    }

    pub fn obj_table_mut(&mut self) -> &mut ObjectTable {
        &mut self.obj_table
    }

    pub fn dict_table(&self) -> &DictionaryTable {
        &self.dict_table
    }
}
