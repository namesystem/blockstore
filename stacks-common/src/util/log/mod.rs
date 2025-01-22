#[cfg(feature = "log")]
#[macro_use]
mod std;

#[cfg(feature = "log")]
pub use self::std::*;

#[cfg(not(feature = "log"))]
#[macro_use]
mod noop;

#[cfg(not(feature = "log"))]
pub use self::noop::*;
