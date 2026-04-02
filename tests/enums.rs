/// Test enum translation with variants.
pub enum Color {
    Red,
    Green,
    Blue,
    Custom(u8, u8, u8),
}

pub fn is_red(c: &Color) -> bool {
    match c {
        Color::Red => true,
        _ => false,
    }
}
