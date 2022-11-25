#[inline]
pub fn unexpected_eof(reason: &'static str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::UnexpectedEof, reason)
}

#[inline]
pub fn invalid_data(reason: &'static str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, reason)
}

#[inline]
pub fn unsupported(reason: &'static str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::Unsupported, reason)
}
