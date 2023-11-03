use std::result::Result;
use core::fmt;
use core::fmt::{Display, Formatter};

#[derive(Debug, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct Either<A, B>(pub Result<A, B>);

impl<A, B> Either<A, B> {
    fn left(a: A) -> Self {
        Self(Ok(a))
    }
    fn right(b: B) -> Self {
        Self(Err(b))
    }
    fn test_left<F>(&self, f: F) -> bool
    where
        F: Fn(&A) -> bool,
    {
        match self.0 {
            Ok(ref a) => f(a),
            _ => false,
        }
    }
    fn test_right<F>(&self, f: F) -> bool
    where
        F: Fn(&B) -> bool,
    {
        match self.0 {
            Err(ref b) => f(b),
            _ => false,
        }
    }
    fn right_or<'a>(&'a self, default: &'a B) -> &'a B {
        match self.0 {
            Ok(_) => default,
            Err(ref e) => e,
        }
    }
}

impl<A: Display, B: Display> Display for Either<A, B> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Ok(ref a) => write!(f, "{}", a),
            Err(ref b) => write!(f, "{}", b),
        }
    }
}


