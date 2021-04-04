use crate::CompiledPat;

// MatchAny {{{

/// Matches anything. Equivalent to any number of `*`s.
#[derive(Debug, Clone)]
pub struct MatchAny;

impl CompiledPat for MatchAny {
    fn matches(&self, _: &str) -> bool {
        true
    }
}

// }}}

// OptionalCharLen {{{

/// Matches some number of optional characters. Equivalent to some number of `?`s.
/// (This is also used to handle the empty pattern.)
#[derive(Debug, Clone)]
pub struct OptionalCharLen {
    /// The number of optional characters.
    pub len: usize,
}

impl CompiledPat for OptionalCharLen {
    fn matches(&self, string: &str) -> bool {
        string.len() == self.len
    }
}

// }}}

// LiteralStr {{{

/// Matches a literal string.
#[derive(Debug, Clone)]
pub struct LiteralStr(pub String);

impl CompiledPat for LiteralStr {
    fn matches(&self, string: &str) -> bool {
        string == self.0
    }
}

// }}}

// General {{{

/// Used in the most general case.  
/// INVARIANT: Must not have multiple wildcards in a row.
#[derive(Debug, Clone)]
pub struct General {
    pub states: Vec<State>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
    Char(char),
    Wildcard,
    UnknownChar,
}

impl CompiledPat for General {
    fn matches(&self, string: &str) -> bool {
        // This is a (Thompson NFA)-inspired nondeterministic finite automaton implementation for wildcard matching.
        // Worst-case time complexity is O((pattern length) * (string length)).
        let state_nr = self.states.len();
        // `active[i] == true` if `states[i]` is active in the current iteration.
        // `states[state_nr]` refers to the final state: in other words, in that state we're
        // expecting EOF.
        let mut active = vec![false; state_nr + 1].into_boxed_slice();
        // The states that will be active in the next iteration.
        let mut active_next = vec![false; state_nr + 1].into_boxed_slice();
        active[0] = true;
        // Initial wildcards *might* be ignored.
        if self.states[0] == State::Wildcard {
            active[1] = true;
        }
        for chr in string.chars() {
            for j in 0..state_nr {
                if active[j] {
                    // Whether or not to `stay` on this state, or `advance` to the next state.
                    // Due to this being a NFA, it is possible to trigger both at once.
                    let (stay, advance) = match self.states[j] {
                        // We can only advance to the next state if the character matches this one.
                        // But we can't stay at this state either.
                        State::Char(expected) => (false, chr == expected),
                        // An `UnknownChar` matches any character (so we advance),
                        // but can't match no characters.
                        State::UnknownChar => (false, true),
                        // Either we stop the wildcard after this `chr` (and advance to the next state),
                        // or we keep continuing the wildcard (and stay at this state).
                        State::Wildcard => (true, true),
                    };
                    active_next[j] |= stay;
                    active_next[j + 1] |= advance;
                    // If the next state is a wildcard it can be automatically skipped.
                    if j + 1 < state_nr && self.states[j + 1] == State::Wildcard {
                        active_next[j + 2] |= advance;
                    }
                }
            }
            dbg!(&active);
            dbg!(&active_next);
            active.swap_with_slice(&mut active_next);
            for j in 0..state_nr + 1 {
                active_next[j] = false;
            }
        }
        // The pattern can only be matched if we are expecting an EOF to end the pattern, and the current string character is an EOF.
        active[state_nr]
    }
}

// }}}
