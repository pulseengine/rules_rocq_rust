/// A simple 2D point structure for demonstration
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

impl Point {
    /// Creates a new point at the origin
    pub fn origin() -> Self {
        Point { x: 0, y: 0 }
    }

    /// Creates a new point with the given coordinates
    pub fn new(x: i32, y: i32) -> Self {
        Point { x, y }
    }

    /// Translates the point by the given delta
    pub fn translate(&mut self, dx: i32, dy: i32) {
        self.x += dx;
        self.y += dy;
    }

    /// Returns the squared distance from the origin
    pub fn squared_distance(&self) -> i32 {
        self.x * self.x + self.y * self.y
    }

    /// Checks if this point is at the origin
    pub fn is_origin(&self) -> bool {
        self.x == 0 && self.y == 0
    }
}

/// A rectangle defined by two corner points
pub struct Rectangle {
    pub top_left: Point,
    pub bottom_right: Point,
}

impl Rectangle {
    /// Creates a new rectangle from two corner points
    pub fn new(top_left: Point, bottom_right: Point) -> Self {
        Rectangle { top_left, bottom_right }
    }

    /// Returns the width of the rectangle
    pub fn width(&self) -> i32 {
        self.bottom_right.x - self.top_left.x
    }

    /// Returns the height of the rectangle
    pub fn height(&self) -> i32 {
        self.bottom_right.y - self.top_left.y
    }
}
