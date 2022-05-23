use std::collections::HashMap;
use std::{io, fs, path::Path};
use std::fmt::{Debug, self, Display};

/// An error used with `Readable` objects.
#[derive(Debug)]
pub enum ReadError<T> {
    /// An IO error.
    Io(io::Error),

    /// A parsing error.
    Parse(T),
}

impl<T> From<io::Error> for ReadError<T> {
    /// Convert an IO error into a `ReadError`.
    fn from(err: io::Error) -> Self {
        ReadError::Io(err)
    }
}

impl<T: Display> Display for ReadError<T> {
    /// Display a `ReadError`.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ReadError::Io(err) => write!(f, "IO error: {}", err),
            ReadError::Parse(err) => write!(f, "Parse error: {}", err),
        }
    }
}

/// An object that can be created from a reader.
pub trait Readable: Sized {
    /// The type of error returned when there is parsing error.
    type ParseError;

    /// Create a new object from a reader.
    /// 
    /// # Arguments
    /// 
    /// * `reader` - The reader to read from.
    /// 
    /// # Errors
    /// 
    /// * `ReadError::Io` - An IO error occurred.
    /// * `ReadError::Parse` - A parsing error occurred.
    fn load<R: io::Read>(reader: &mut R) -> Result<Self, ReadError<Self::ParseError>>;

    /// Create a new object from a file.
    /// 
    /// # Arguments
    /// 
    /// * `path` - The path to the file to read from.
    /// 
    /// # Errors
    /// 
    /// * `ReadError::Io` - An IO error occurred.
    /// * `ReadError::Parse` - A parsing error occurred.
    fn load_file<P: AsRef<Path>>(path: P) -> Result<Self, ReadError<Self::ParseError>> {
        Self::load(&mut fs::File::open(path)?)
    }

    /// Get all objects from a directory (one object per file).
    /// 
    /// If a file cannot be loaded, it is ignored.
    /// If the directory does not exist, an empty map is returned.
    /// 
    /// # Arguments
    /// 
    /// * `path` - The path to the directory to read from.
    fn load_all<P: AsRef<Path>>(path: P) -> HashMap<String, Self> {
        let mut map = HashMap::new();
        if let Ok(entries) = fs::read_dir(path) {
            for entry in entries {
                if let Ok(entry) = entry {
                    if let Some(name) = entry.file_name().to_str() {
                        if let Ok(obj) = Self::load_file(entry.path()) {
                            map.insert(name.to_owned(), obj);
                        }
                    }
                }
            }
        }
        map
    }
}
