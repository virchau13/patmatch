//! A configurable pattern matching (also known as globbing) library.
//!
//! The general use of this library is to compile `Pattern`s, then use them. For example:
//!
//! ```rust
//! use patmatch::{Pattern, MatchOptions};
//! let pat = Pattern::compile("*.png", MatchOptions::ALL);
//! assert!(pat.matches("file.png"));
//! assert!(!pat.matches("file.jpeg"));
//! ```

mod compiled;
pub mod options;
pub use options::*;

use dyn_clone::DynClone;
use std::{
    fmt,
    iter::FromIterator,
    iter::{FusedIterator, Peekable},
};

/// A pattern to match strings against.
#[derive(Debug, Clone)]
pub struct Pattern {
    pat: Box<dyn CompiledPat>,
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.pat.fmt(f)
    }
}

/// A trait for compiled patterns.
trait CompiledPat: fmt::Debug + DynClone {
    /// See [`Pattern::matches`], which calls this.
    fn matches(&self, string: &str) -> bool;
}

dyn_clone::clone_trait_object!(CompiledPat);

/// A part of a [`Pattern`].
/// Used to configure a compiled Pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Chunk {
    /// A literal string. This matches the string exactly.
    Str(String),
    /// A wildcard (usually represented by an asterisk).
    /// Matches any amount of characters, including none.
    Wildcard,
    /// An unknown character (usually represented by a question mark).
    UnknownChar,
}

impl Chunk {
    /// Turns `chr` into any of the non-[`Chunk::Str`] variants (e.g. [`Chunk::Wildcard`], etc.)
    /// Only really used for ease of implementation of [`Pattern::compile`].
    fn from_char(chr: char) -> Option<Chunk> {
        use Chunk::*;
        match chr {
            '*' => Some(Wildcard),
            '?' => Some(UnknownChar),
            _ => None,
        }
    }
    pub fn str(s: &str) -> Chunk {
        Chunk::Str(s.to_owned())
    }
    fn take_str(self) -> Option<String> {
        match self {
            Chunk::Str(s) => Some(s),
            _ => None,
        }
    }
}

impl From<String> for Chunk {
    fn from(s: String) -> Self {
        Chunk::Str(s)
    }
}

impl FromIterator<Chunk> for Pattern {
    /// Used to compile a `Pattern` from an iterator of [`Chunk`]s.
    /// Note that this allocates memory to store *all* the `Chunk`s.
    ///
    /// Example usage:
    /// ```rust
    /// use patmatch::{Pattern, Chunk};
    /// let chunk_vec = vec![Chunk::str("IMG_"), Chunk::Wildcard, Chunk::str(".png")];
    /// let pat: Pattern = chunk_vec.into_iter().collect();
    /// assert!(pat.matches("IMG_20170301.png"));
    /// assert!(!pat.matches("stuff.png")); assert!(!pat.matches("IMG_20170302.jpeg"));
    /// ```
    fn from_iter<T: IntoIterator<Item = Chunk>>(iter: T) -> Self {
        use compiled::*;
        dbg!("HI!");
        let mut chunks = Vec::new();
        for chunk in iter {
            if !(chunk == Chunk::Wildcard && chunks.ends_with(&[Chunk::Wildcard])) {
                chunks.push(chunk);
            }
        }
        let chunks = chunks;
        dbg!(&chunks);
        if chunks.iter().all(|chunk| chunk == &Chunk::UnknownChar) {
            // (Also handles the empty string.)
            Pattern::from_compiled(OptionalCharLen { len: chunks.len() })
        } else if chunks.iter().all(|chunk| chunk == &Chunk::Wildcard) {
            Pattern::from_compiled(MatchAny {})
        } else if chunks.iter().all(|chunk| matches!(chunk, Chunk::Str(_))) {
            Pattern::from_compiled(LiteralStr(
                chunks.into_iter().map(|x| x.take_str().unwrap()).collect(),
            ))
        } else {
            let mut states = Vec::new();
            for chunk in chunks {
                match chunk {
                    Chunk::Wildcard => states.push(State::Wildcard),
                    Chunk::UnknownChar => states.push(State::UnknownChar),
                    Chunk::Str(string) => {
                        for chr in string.chars() {
                            states.push(State::Char(chr));
                        }
                    }
                }
            }
            Pattern::from_compiled(General { states })
        }
    }
}

/// An iterator for yielding `Chunk`s from an iterator.
struct CompileIter<T: Iterator<Item = char>> {
    iter: Peekable<T>,
    opts: MatchOptions,
}
impl<T: Iterator<Item = char>> Iterator for CompileIter<T> {
    type Item = Chunk;
    fn next(&mut self) -> Option<Self::Item> {
        use Chunk::*;
        match self.iter.next() {
            None => None,
            Some(chr) => Some(match chr {
                c if self.opts.contains(c.into()) => Chunk::from_char(c).unwrap(),
                _ => {
                    let mut string = String::new();
                    string.push(chr);
                    loop {
                        dbg!("ok");
                        match self.iter.peek() {
                            Some(peeked) if !self.opts.contains(MatchOptions::from(*peeked)) => {
                                string.push(*peeked);
                                self.iter.next();
                            }
                            _ => break,
                        }
                    }
                    Str(string)
                }
            }),
        }
    }
}

impl<T: Iterator<Item = char>> FusedIterator for CompileIter<T> {}

impl Pattern {
    /// Compiles a pattern from a string, using shell-like syntax.
    /// If you want to compile your own custom string format, see [`Pattern::from_iter`].
    ///
    /// Each of these can be toggled using [`MatchOptions`].
    /// * All characters prefixed with a backslash (`\`) are interpreted literally.
    /// * ([`MatchOptions::WILDCARDS`]) Asterisks (`*`s) are interpreted as wildcards: e.g. `a*b` is interpreted as `a`, a
    /// wildcard then `b`.
    /// * ([`MatchOptions::UNKNOWN_CHARS`]) Question marks (`?`s) are interpreted as optional characters.
    pub fn compile(pat: &str, opts: MatchOptions) -> Pattern {
        // Yield all chunks and collect them into a `Pattern`.
        CompileIter {
            iter: pat.chars().peekable(),
            opts,
        }
        .collect()
    }

    /// The same as [`Pattern::compile`], but with an iterator instead of a `&str`.
    pub fn compile_iter<T: IntoIterator<Item = char>>(pat: T, opts: MatchOptions) -> Pattern {
        CompileIter {
            iter: pat.into_iter().peekable(),
            opts,
        }
        .collect()
    }

    /// Checks if `string` matches the pattern.
    /// The pattern is checked for a match "perfectly",
    /// i.e. if it is possible to match by choosing all of the matches optimally,
    /// it will do so.
    /// This optimizes matching checks if not all features are used.
    pub fn matches(&self, string: &str) -> bool {
        self.pat.matches(string)
    }

    fn from_compiled<T: CompiledPat + 'static>(pat: T) -> Pattern {
        Pattern { pat: Box::new(pat) }
    }
}

#[cfg(test)]
mod tests {
    use super::{Chunk, MatchOptions, Pattern};
    use Chunk::*;

    /// Checks the match status of all patterns in `patterns` against all strings in `strings`.
    fn check_match(patterns: Vec<Pattern>, strings: Vec<&str>, expected: bool) {
        for pat in patterns {
            for string in strings.iter() {
                assert_eq!(
                    pat.matches(string),
                    expected,
                    "Pattern {} failed to match against {}",
                    pat,
                    string
                );
            }
        }
    }

    fn matches(patterns: Vec<Pattern>, strings: Vec<&str>) {
        check_match(patterns, strings, true)
    }

    fn matches_v(patterns: Vec<Vec<Chunk>>, strings: Vec<&str>) {
        matches(
            patterns
                .into_iter()
                .map(|v| v.into_iter().collect())
                .collect(),
            strings,
        )
    }

    fn strings_to_pats(patterns: Vec<&str>) -> Vec<Pattern> {
        patterns
            .into_iter()
            .map(|pat| Pattern::compile(pat, MatchOptions::ALL))
            .collect()
    }

    fn matches_s(patterns: Vec<&str>, strings: Vec<&str>) {
        matches(
            strings_to_pats(patterns),
            strings,
        )
    }

    fn no_match_s(patterns: Vec<&str>, strings: Vec<&str>) {
        check_match(
            strings_to_pats(patterns),
            strings,
            false
        )
    }

    macro_rules! chunk {
        ($i:ident) => {
            $i
        };
        ($s:tt) => {
            Str($s.to_string())
        };
    }
    macro_rules! chunks {
        ($($t:tt),*) => {
            vec![ $(chunk!($t)),* ]
        }
    }

    #[test]
    fn cat() {
        matches_v(vec![chunks!["c", UnknownChar, "t"]], vec!["cat"]);
        matches_s(
            vec![
                "*", "c*", "*t", "*a*", "c*t", "ca*", "*at", "???", "?a?", "c??", "??t", "ca?",
                "?at", "c?t", "cat", "ca*t", "c*at", "*cat", "cat*", "ca****t"
            ],
            vec!["cat"]
        );
        no_match_s(
            vec![
                "cat?", "?cat", "c?at", "ca?t", "?", "??", "????", "", " *"
            ],
            vec!["cat"]
        );
    }

    #[test]
    fn empty() {
        matches_s(
            vec![""],
            vec![""]
        );
        no_match_s(
            vec![""],
            vec!["a", "b", "c", " ", "\t", "\n"]
        );
    }
}
