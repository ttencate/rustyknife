use crate::errors::RuntimeError;

// TODO implement
pub struct AbbreviationsTable();

pub struct ZString<'a>(&'a[u8]);

impl<'a> ZString<'a> {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn decode(&self, _abbrs_table: &AbbreviationsTable) -> Result<String, RuntimeError> {
        panic!("TODO zstring decoding is not yet implemented");
    }
}

impl<'a> From<&'a[u8]> for ZString<'a> {
    fn from(bytes: &[u8]) -> ZString {
        ZString(bytes)
    }
}
