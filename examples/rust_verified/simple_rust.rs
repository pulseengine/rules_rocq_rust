// Simple Rust code for verification demonstration
// This will be translated to Coq using coq-of-rust

/// A simple struct representing a point in 2D space
#[derive(Debug, Clone, Copy)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

impl Point {
    /// Create a new point
    pub fn new(x: i32, y: i32) -> Self {
        Point { x, y }
    }

    /// Calculate the distance from origin (simplified)
    pub fn distance_from_origin(&self) -> i32 {
        self.x.abs() + self.y.abs()
    }

    /// Add two points together
    pub fn add(&self, other: &Point) -> Point {
        Point {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }

    /// Check if point is at origin
    pub fn is_origin(&self) -> bool {
        self.x == 0 && self.y == 0
    }
}

/// A simple function that works with points
pub fn create_and_manipulate_point() -> Point {
    let p1 = Point::new(3, 4);
    let p2 = Point::new(1, 2);
    p1.add(&p2)
}

/// Function to check if a point is valid (non-negative coordinates)
pub fn is_valid_point(p: &Point) -> bool {
    p.x >= 0 && p.y >= 0
}

// Main function for demonstration
pub fn main() {
    let point = create_and_manipulate_point();
    println!("Created point: {:?}", point);
    println!("Distance from origin: {}", point.distance_from_origin());
    println!("Is origin: {}", point.is_origin());
    println!("Is valid: {}", is_valid_point(&point));
}