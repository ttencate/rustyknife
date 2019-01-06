use crate::bytes::Bytes;
use crate::errors::FormatError;
use crate::globals::GlobalsTable;
use crate::header::Header;
use crate::obj::ObjectTable;
use crate::version::Version;
use crate::zstring::AbbreviationsTable;

pub struct Memory<'a> {
    version: Version,
    bytes: &'a mut Bytes,
    header: Header<'a>,
    globals_table: GlobalsTable<'a>,
    obj_table: ObjectTable<'a>,
    abbrs_table: AbbreviationsTable<'a>,
}

impl<'a> Memory<'a> {
    pub fn wrap(bytes: &mut Bytes) -> Result<Memory, FormatError> {
        let header = Header::new(bytes)?;
        let version = header.version();
        let globals_table = GlobalsTable::new(version, bytes, header.globals_table_addr())?;
        let abbrs_table = AbbreviationsTable::new(version, bytes, header.abbrs_table_addr())?;
        let obj_table = ObjectTable::new(version, bytes, header.obj_table_addr(), &abbrs_table)?;

        Ok(Memory {
            version: version,
            bytes: bytes,
            header: header,
            globals_table: globals_table,
            abbrs_table: abbrs_table,
            obj_table: obj_table,
        })
    }

    pub fn version(&self) -> Version {
        self.version
    }

    pub fn header(&self) -> &Header {
        &self.header
    }

    pub fn header_mut(&mut self) -> &mut Header<'a> {
        &mut self.header
    }

    pub fn bytes(&self) -> &Bytes {
        &self.bytes
    }

    pub fn bytes_mut(&mut self) -> &mut Bytes {
        &mut self.bytes
    }

    pub fn globals(&self) -> &GlobalsTable {
        &self.globals_table
    }

    pub fn globals_mut(&mut self) -> &mut GlobalsTable<'a> {
        &mut self.globals_table
    }

    pub fn abbrs_table(&self) -> &AbbreviationsTable {
        &self.abbrs_table
    }

    pub fn obj_table(&self) -> &ObjectTable {
        &self.obj_table
    }

    pub fn obj_table_mut(&mut self) -> &mut ObjectTable<'a> {
        &mut self.obj_table
    }
}
