pub trait BooleanAlg {
    pub fn and(a: &Self, b: &Self) -> Self;
    pub fn or(a: &Self, b: &Self) -> Self;
}
