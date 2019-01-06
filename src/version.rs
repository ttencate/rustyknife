use crate::errors::FormatError;

#[repr(u8)]
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum Version {
    V1 = 1,
    V2 = 2,
    V3 = 3,
}

pub use self::Version::*;

impl Version {
    // When TryFrom is graduated from nightly, we can implement that with the same signature.
    pub fn try_from(byte: u8) -> Result<Version, FormatError> {
        match byte {
            1 => Ok(V1),
            2 => Ok(V2),
            3 => Ok(V3),
            _ => Err(FormatError::UnsupportedVersion(byte))
        }
    }
}
