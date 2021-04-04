//! Options for configuring the pattern matching.

use bitflags::bitflags;

bitflags! {
    /// The features that will be looked for when using
    /// [`Pattern::compile`](crate::Pattern::compile).
    ///
    /// For example, if an asterisk `*` is present in the pattern,
    /// it will be interpreted as a wildcard only if [`MatchOptions::WILDCARDS`] is present.
    pub struct MatchOptions: u8 {
        /// No match options. In other words, use no special features whatsoever.
        /// Should not be used in most cases.
        const NONE = 1 << 7;
        /// Whether or not to use wildcards. See [`Chunk::Wildcard`].
        const WILDCARDS = 1;
        /// Whether or not to use optional characters. See [`Chunk::OptionalChar`].
        const UNKNOWN_CHARS = 1 << 1;
        /// All possible options.
        const ALL = 255 ^ (1 << 7);
    }
}

impl From<char> for MatchOptions {
    /// Checks if `chr` is a special character or not.
    /// Returns [`MatchOptions::ALL`] if it is not.
    fn from(chr: char) -> Self {
        match chr {
            '*' => MatchOptions::WILDCARDS,
            '?' => MatchOptions::UNKNOWN_CHARS,
            _ => MatchOptions::NONE,
        }
    }
}
