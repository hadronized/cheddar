use std::fmt;
use std::error::Error;
use std::path::PathBuf;
use warmy::FSKey;

use parser::ParseError;

#[derive(Debug)]
pub enum ModuleError {
  FileNotFound(PathBuf),
  ParseFailed(ParseError),
  IncompleteInput,
  DepsError(DepsError)
}

impl fmt::Display for ModuleError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      ModuleError::FileNotFound(ref path) => write!(f, "file not found: {}", path.display()),
      ModuleError::ParseFailed(ref e) => write!(f, "parse failed: {}", e),
      ModuleError::IncompleteInput => f.write_str("incomplete input"),
      ModuleError::DepsError(ref e) => write!(f, "dependency error: {}", e)
    }
  }
}

impl Error for ModuleError {
  fn description(&self) -> &str {
    match *self {
      ModuleError::FileNotFound(_) => "file not found",
      ModuleError::ParseFailed(_) => "parse failed",
      ModuleError::IncompleteInput => "incomplete input",
      ModuleError::DepsError(_) => "error in dependencies"
    }
  }

  fn cause(&self) -> Option<&Error> {
    match *self {
      ModuleError::ParseFailed(ref e) => Some(e),
      ModuleError::DepsError(ref e) => Some(e),
      _ => None
    }
  }
}

/// Errors that can happen in dependencies.
#[derive(Debug)]
pub enum DepsError {
  /// If a module’s dependencies has any cycle, the dependencies are unusable and the cycle is
  /// returned.
  Cycle(FSKey, FSKey),
  /// There was a loading error of a module.
  LoadError(FSKey, Box<Error>),
}

impl fmt::Display for DepsError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      DepsError::Cycle(ref a, ref b) => write!(f, "dependency cycle between {} and {}", a.as_path().display(), b.as_path().display()),
      DepsError::LoadError(ref key, ref e) => write!(f, "load error for {}: {}", key.as_path().display(), e)
    }
  }
}

impl Error for DepsError {
  fn description(&self) -> &str {
    match *self {
      DepsError::Cycle(..) => "module cycle",
      DepsError::LoadError(..) => "load error",
    }
  }

  fn cause(&self) -> Option<&Error> {
    match *self {
      DepsError::LoadError(_, ref e) => Some(e.as_ref()),
      _ => None
    }
  }
}
