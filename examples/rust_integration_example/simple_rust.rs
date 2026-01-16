// Simple Rust example for integration demonstration
// This would be translated to Coq using our integration

/// A simple struct for demonstration
pub struct Point {
    pub x: i32,
    pub y: i32,
}

impl Point {
    /// Create a new point
    pub fn new(x: i32, y: i32) -> Self {
        Point { x, y }
    }

    /// Calculate Manhattan distance from origin
    pub fn distance(&self) -> i32 {
        self.x.abs() + self.y.abs()
    }
}

/// Simple function to create and use a point
pub fn create_point() -> Point {
    Point::new(3, 4)
}

/// Main function for demonstration
pub fn main() {
    let point = create_point();
    println!("Point: ({}, {})", point.x, point.y);
    println!("Distance: {}", point.distance());
}