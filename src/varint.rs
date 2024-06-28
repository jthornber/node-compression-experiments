use byteorder::{ReadBytesExt, WriteBytesExt};
use std::io::{self, Read, Write};

//----------------------------------------------------------------

pub fn write_varint<W: Write>(writer: &mut W, mut value: u64) -> io::Result<()> {
    while value > 0x7F {
        writer.write_u8(((value & 0x7F) | 0x80) as u8)?;
        value >>= 7;
    }
    writer.write_u8(value as u8)?;
    Ok(())
}

pub fn read_varint<R: Read>(reader: &mut R) -> io::Result<u64> {
    let mut value = 0u64;
    for i in 0..10 {
        // max 10 bytes for a 64-bit varint
        let byte = reader.read_u8()?;
        if i == 9 && byte > 1 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "varint overflows 64 bits",
            ));
        }
        value |= ((byte & 0x7F) as u64) << (i * 7);
        if byte & 0x80 == 0 {
            return Ok(value);
        }
    }
    Err(io::Error::new(
        io::ErrorKind::InvalidData,
        "varint too long",
    ))
}

//----------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn test_varint_roundtrip() {
        let test_values = vec![
            0,
            1,
            127,
            128,
            255,
            256,
            16383,
            16384,
            2097151,
            2097152,
            268435455,
            268435456,
            0x7FFFFFFFFFFFFFFF,
            u64::MAX,
        ];

        for value in test_values {
            let mut buf = Vec::new();
            write_varint(&mut buf, value).unwrap();

            let mut reader = Cursor::new(buf);
            let decoded = read_varint(&mut reader).unwrap();

            assert_eq!(value, decoded, "Failed for value: {}", value);
        }
    }

    #[test]
    fn test_varint_size() {
        let test_cases = vec![
            (0, 1),
            (127, 1),
            (128, 2),
            (16383, 2),
            (16384, 3),
            (2097151, 3),
            (2097152, 4),
            (268435455, 4),
            (268435456, 5),
            (0x7FFFFFFFFFFFFFFF, 9),
            (u64::MAX, 10),
        ];

        for (value, expected_size) in test_cases {
            let mut buf = Vec::new();
            write_varint(&mut buf, value).unwrap();
            assert_eq!(
                buf.len(),
                expected_size,
                "Unexpected size for value: {}",
                value
            );
        }
    }

    #[test]
    fn test_varint_max_value() {
        let max_value = u64::MAX;
        let mut buf = Vec::new();
        write_varint(&mut buf, max_value).unwrap();

        let mut reader = Cursor::new(buf);
        let decoded = read_varint(&mut reader).unwrap();

        assert_eq!(max_value, decoded, "Failed for max value");
    }

    #[test]
    fn test_varint_long_encoding() {
        // This encodes the value 1 in a deliberately long way
        let long_encoding = vec![0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x01];
        let expected_value = 9295997013522923649; // 0x8101010101010101
        let mut reader = Cursor::new(long_encoding);
        let decoded = read_varint(&mut reader).unwrap();
        assert_eq!(
            decoded, expected_value,
            "Long encoding should still decode correctly"
        );
    }

    #[test]
    fn test_varint_invalid_too_long() {
        // This encodes a value with more than 10 bytes, which should be invalid
        let invalid_encoding = vec![0x81; 11];
        let mut reader = Cursor::new(invalid_encoding);
        let result = read_varint(&mut reader);
        assert!(result.is_err(), "Varint too long should result in an error");
    }
}
