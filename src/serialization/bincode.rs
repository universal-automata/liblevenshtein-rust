//! Bincode serializer for compact binary format.

use crate::dictionary::Dictionary;
use std::io::{Read, Write};

use super::{extract_terms, DictionaryFromTerms, DictionarySerializer, SerializationError};

/// Bincode serializer for compact binary format.
///
/// This serializer uses bincode for fast, space-efficient serialization.
/// It's ideal for production use where storage space and load time matter.
pub struct BincodeSerializer;

impl DictionarySerializer for BincodeSerializer {
    fn serialize<D, W>(dict: &D, mut writer: W) -> Result<(), SerializationError>
    where
        D: Dictionary,
        W: Write,
    {
        let terms = extract_terms(dict);
        bincode::serialize_into(&mut writer, &terms)?;
        Ok(())
    }

    fn deserialize<D, R>(mut reader: R) -> Result<D, SerializationError>
    where
        D: DictionaryFromTerms,
        R: Read,
    {
        let terms: Vec<String> = bincode::deserialize_from(&mut reader)?;
        Ok(D::from_terms(terms))
    }
}
