// Rust code for integration example
// This demonstrates how to integrate with rules_rust

/// A simple data structure
#[derive(Debug, Clone)]
pub struct DataPoint {
    pub value: i32,
    pub timestamp: u64,
}

impl DataPoint {
    /// Create a new data point
    pub fn new(value: i32, timestamp: u64) -> Self {
        DataPoint { value, timestamp }
    }

    /// Validate the data point
    pub fn is_valid(&self) -> bool {
        self.value >= 0 && self.timestamp > 0
    }

    /// Update the value
    pub fn update_value(&mut self, new_value: i32) {
        if new_value >= 0 {
            self.value = new_value;
        }
    }
}

/// Process a collection of data points
pub fn process_data_points(points: &[DataPoint]) -> Vec<i32> {
    points.iter()
        .filter(|p| p.is_valid())
        .map(|p| p.value)
        .collect()
}

/// Calculate statistics
pub fn calculate_stats(points: &[DataPoint]) -> (i32, i32, f64) {
    let valid_points: Vec<&DataPoint> = points.iter().filter(|p| p.is_valid()).collect();
    
    if valid_points.is_empty() {
        return (0, 0, 0.0);
    }
    
    let sum: i32 = valid_points.iter().map(|p| p.value).sum();
    let count = valid_points.len() as i32;
    let average = sum as f64 / count as f64;
    
    (sum, count, average)
}

// Main function for testing
pub fn main() {
    let mut point1 = DataPoint::new(42, 1000);
    let point2 = DataPoint::new(-5, 2000); // Invalid
    let point3 = DataPoint::new(100, 3000);
    
    println!("Point 1 valid: {}", point1.is_valid());
    println!("Point 2 valid: {}", point2.is_valid());
    
    point1.update_value(50);
    println!("Updated point 1 value: {}", point1.value);
    
    let points = vec![point1, point2, point3];
    let processed = process_data_points(&points);
    println!("Processed values: {:?}", processed);
    
    let (sum, count, avg) = calculate_stats(&points);
    println!("Stats - Sum: {}, Count: {}, Avg: {}", sum, count, avg);
}