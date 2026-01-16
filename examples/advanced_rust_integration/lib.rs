//! Advanced Rust integration example
//! This demonstrates complex Rust patterns that can be verified with coq-of-rust

/// A module for mathematical operations
pub mod math {
    /// Safe addition that checks for overflow
    pub fn safe_add(a: i32, b: i32) -> Option<i32> {
        a.checked_add(b)
    }
    
    /// Safe subtraction that checks for overflow
    pub fn safe_sub(a: i32, b: i32) -> Option<i32> {
        a.checked_sub(b)
    }
    
    /// Greatest common divisor using Euclidean algorithm
    pub fn gcd(mut a: u32, mut b: u32) -> u32 {
        while b != 0 {
            let temp = b;
            b = a % b;
            a = temp;
        }
        a
    }
    
    /// Least common multiple
    pub fn lcm(a: u32, b: u32) -> Option<u32> {
        a.checked_mul(b).and_then(|prod| prod.checked_div(gcd(a, b)))
    }
}

/// A module for data structures
pub mod data {
    /// A simple generic Result type
    pub enum Result<T, E> {
        Ok(T),
        Err(E),
    }
    
    /// A simple Option type
    pub enum Option<T> {
        Some(T),
        None,
    }
    
    /// A simple linked list
    pub struct List<T> {
        head: Option<Box<Node<T>>>, 
    }
    
    struct Node<T> {
        value: T,
        next: Option<Box<Node<T>>>, 
    }
    
    impl<T> List<T> {
        pub fn new() -> Self {
            List { head: Option::None }
        }
        
        pub fn push(&mut self, value: T) {
            let new_node = Box::new(Node {
                value,
                next: self.head.take(),
            });
            self.head = Option::Some(new_node);
        }
        
        pub fn pop(&mut self) -> Option<T> {
            self.head.take().map(|node| {
                self.head = node.next;
                node.value
            })
        }
    }
}

/// A module for state machines
pub mod state_machine {
    /// A simple traffic light state machine
    #[derive(Debug, PartialEq)]
    pub enum TrafficLight {
        Red,
        Yellow,
        Green,
    }
    
    pub struct TrafficLightController {
        state: TrafficLight,
        timer: u32,
    }
    
    impl TrafficLightController {
        pub fn new() -> Self {
            TrafficLightController {
                state: TrafficLight::Red,
                timer: 0,
            }
        }
        
        pub fn tick(&mut self) {
            self.timer += 1;
            
            match self.state {
                TrafficLight::Red => {
                    if self.timer >= 30 {
                        self.state = TrafficLight::Green;
                        self.timer = 0;
                    }
                }
                TrafficLight::Green => {
                    if self.timer >= 20 {
                        self.state = TrafficLight::Yellow;
                        self.timer = 0;
                    }
                }
                TrafficLight::Yellow => {
                    if self.timer >= 5 {
                        self.state = TrafficLight::Red;
                        self.timer = 0;
                    }
                }
            }
        }
        
        pub fn get_state(&self) -> TrafficLight {
            self.state.clone()
        }
    }
}

/// A module for property-based testing patterns
pub mod properties {
    /// Check if a number is prime
    pub fn is_prime(n: u32) -> bool {
        if n <= 1 {
            return false;
        }
        if n == 2 {
            return true;
        }
        if n % 2 == 0 {
            return false;
        }
        
        let sqrt_n = (n as f64).sqrt() as u32 + 1;
        for i in (3..sqrt_n).step_by(2) {
            if n % i == 0 {
                return false;
            }
        }
        true
    }
    
    /// Generate the nth Fibonacci number
    pub fn fibonacci(n: u32) -> u64 {
        if n == 0 {
            0
        } else if n == 1 {
            1
        } else {
            let mut a = 0;
            let mut b = 1;
            for _ in 2..=n {
                let c = a + b;
                a = b;
                b = c;
            }
            b
        }
    }
}

// Main function for testing
fn main() {
    println!("Advanced Rust integration example");
    
    // Test math operations
    println!("Math operations:");
    println!("  safe_add(10, 20) = {:?}", math::safe_add(10, 20));
    println!("  safe_add(i32::MAX, 1) = {:?}", math::safe_add(i32::MAX, 1));
    println!("  gcd(48, 18) = {}", math::gcd(48, 18));
    println!("  lcm(4, 6) = {:?}", math::lcm(4, 6));
    
    // Test data structures
    println!("\nData structures:");
    let mut list = data::List::new();
    list.push(1);
    list.push(2);
    list.push(3);
    println!("  Pushed 1, 2, 3 to list");
    println!("  Popped: {:?}", list.pop());
    println!("  Popped: {:?}", list.pop());
    
    // Test state machine
    println!("\nState machine:");
    let mut traffic_light = state_machine::TrafficLightController::new();
    println!("  Initial state: {:?}", traffic_light.get_state());
    for _ in 0..35 {
        traffic_light.tick();
    }
    println!("  After 35 ticks: {:?}", traffic_light.get_state());
    
    // Test properties
    println!("\nProperties:");
    println!("  is_prime(17) = {}", properties::is_prime(17));
    println!("  is_prime(18) = {}", properties::is_prime(18));
    println!("  fibonacci(10) = {}", properties::fibonacci(10));
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_math_operations() {
        assert_eq!(math::safe_add(5, 7), Some(12));
        assert_eq!(math::safe_add(i32::MAX, 1), None);
        assert_eq!(math::gcd(48, 18), 6);
        assert_eq!(math::lcm(4, 6), Some(12));
    }
    
    #[test]
    fn test_data_structures() {
        let mut list = data::List::new();
        assert_eq!(list.pop(), None);
        
        list.push(42);
        assert_eq!(list.pop(), Some(42));
        assert_eq!(list.pop(), None);
    }
    
    #[test]
    fn test_state_machine() {
        let mut controller = state_machine::TrafficLightController::new();
        assert_eq!(controller.get_state(), state_machine::TrafficLight::Red);
        
        // Advance through states
        for _ in 0..30 { controller.tick(); }
        assert_eq!(controller.get_state(), state_machine::TrafficLight::Green);
        
        for _ in 0..20 { controller.tick(); }
        assert_eq!(controller.get_state(), state_machine::TrafficLight::Yellow);
        
        for _ in 0..5 { controller.tick(); }
        assert_eq!(controller.get_state(), state_machine::TrafficLight::Red);
    }
    
    #[test]
    fn test_properties() {
        assert!(properties::is_prime(2));
        assert!(properties::is_prime(3));
        assert!(properties::is_prime(5));
        assert!(!properties::is_prime(4));
        assert!(!properties::is_prime(9));
        
        assert_eq!(properties::fibonacci(0), 0);
        assert_eq!(properties::fibonacci(1), 1);
        assert_eq!(properties::fibonacci(2), 1);
        assert_eq!(properties::fibonacci(10), 55);
    }
}
