/// Test struct with impl block methods.
pub struct Counter {
    pub value: u32,
}

impl Counter {
    pub fn new() -> Self {
        Counter { value: 0 }
    }

    pub fn increment(&self) -> Self {
        Counter {
            value: self.value + 1,
        }
    }

    pub fn get(&self) -> u32 {
        self.value
    }
}
