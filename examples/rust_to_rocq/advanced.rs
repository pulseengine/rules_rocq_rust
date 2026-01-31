// Advanced Rust features for rocq-of-rust translation testing
// Tests: generics, traits, lifetimes, associated types

/// Generic container with a single element
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Container<T> {
    pub value: T,
}

impl<T> Container<T> {
    pub fn new(value: T) -> Self {
        Container { value }
    }

    pub fn get(&self) -> &T {
        &self.value
    }

    pub fn set(&mut self, value: T) {
        self.value = value;
    }

    pub fn into_inner(self) -> T {
        self.value
    }
}

/// Generic pair of two values
#[derive(Debug, Clone)]
pub struct Pair<A, B> {
    pub first: A,
    pub second: B,
}

impl<A, B> Pair<A, B> {
    pub fn new(first: A, second: B) -> Self {
        Pair { first, second }
    }

    pub fn swap(self) -> Pair<B, A> {
        Pair {
            first: self.second,
            second: self.first,
        }
    }
}

/// Trait for types that can be doubled
pub trait Double {
    fn double(&self) -> Self;
}

impl Double for i32 {
    fn double(&self) -> Self {
        self * 2
    }
}

impl Double for i64 {
    fn double(&self) -> Self {
        self * 2
    }
}

/// Generic function using trait bounds
pub fn double_value<T: Double + Clone>(x: &T) -> T {
    x.double()
}

/// Struct with lifetime parameter
pub struct Borrowed<'a, T> {
    pub reference: &'a T,
}

impl<'a, T> Borrowed<'a, T> {
    pub fn new(reference: &'a T) -> Self {
        Borrowed { reference }
    }

    pub fn get(&self) -> &T {
        self.reference
    }
}

/// Option-like enum for testing
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Maybe<T> {
    Just(T),
    Nothing,
}

impl<T> Maybe<T> {
    pub fn is_just(&self) -> bool {
        match self {
            Maybe::Just(_) => true,
            Maybe::Nothing => false,
        }
    }

    pub fn is_nothing(&self) -> bool {
        !self.is_just()
    }

    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Maybe::Just(v) => v,
            Maybe::Nothing => default,
        }
    }

    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Maybe<U> {
        match self {
            Maybe::Just(v) => Maybe::Just(f(v)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

/// Result-like enum for testing
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome<T, E> {
    Ok(T),
    Err(E),
}

impl<T, E> Outcome<T, E> {
    pub fn is_ok(&self) -> bool {
        match self {
            Outcome::Ok(_) => true,
            Outcome::Err(_) => false,
        }
    }

    pub fn is_err(&self) -> bool {
        !self.is_ok()
    }

    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Outcome::Ok(v) => v,
            Outcome::Err(_) => default,
        }
    }
}
