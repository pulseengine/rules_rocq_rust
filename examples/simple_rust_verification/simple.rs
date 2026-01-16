/// Simple Rust function for verification
/// This demonstrates how to write Rust code that can be verified with coq-of-rust

/// A simple function that adds two numbers
/// This will be translated to Coq for formal verification
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

/// A function that checks if a number is even
/// This demonstrates more complex logic that can be verified
pub fn is_even(n: i32) -> bool {
    n % 2 == 0
}

/// A function that computes factorial
/// This shows recursive functions that can be verified
pub fn factorial(n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

/// A function that demonstrates pattern matching
/// This shows how match expressions are translated to Coq
pub fn describe_number(n: i32) -> &'static str {
    match n {
        n if n < 0 => "negative",
        0 => "zero",
        1 => "one",
        _ => "positive"
    }
}

// Main function for testing
fn main() {
    println!("Rust verification example");
    println!("add(2, 3) = {}", add(2, 3));
    println!("is_even(4) = {}", is_even(4));
    println!("factorial(5) = {}", factorial(5));
    println!("describe_number(-5) = {}", describe_number(-5));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
        assert_eq!(add(-1, 1), 0);
    }

    #[test]
    fn test_is_even() {
        assert!(is_even(4));
        assert!(!is_even(3));
    }

    #[test]
    fn test_factorial() {
        assert_eq!(factorial(0), 1);
        assert_eq!(factorial(1), 1);
        assert_eq!(factorial(5), 120);
    }
}
