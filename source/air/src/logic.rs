//! The SMT-LIB logic a query is solved under.

use std::fmt;

/// An SMT-LIB logic.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Logic {
    /// Quantifier-free bit-vectors.
    QfBv,
    /// Bit-vectors, with quantifiers.
    Bv,
    /// Quantifier-free bit-vectors and IEEE floating point.
    QfBvFp,
    /// Bit-vectors and IEEE floating point, with quantifiers.
    BvFp,
    /// All supported theories.
    #[default]
    All,
}

impl Logic {
    /// The SMT-LIB logic name.
    pub fn as_str(&self) -> &'static str {
        match self {
            Logic::QfBv => "QF_BV",
            Logic::Bv => "BV",
            Logic::QfBvFp => "QF_BVFP",
            Logic::BvFp => "BVFP",
            Logic::All => "ALL",
        }
    }
}

impl fmt::Display for Logic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}
