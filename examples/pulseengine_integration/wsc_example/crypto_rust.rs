// Example Rust cryptographic code for wsc integration
// This demonstrates how to verify Rust cryptographic implementations with coq-of-rust

/// Simple cryptographic hash function
pub fn simple_hash(data: &[u8]) -> u64 {
    data.iter().fold(0u64, |acc, &x| acc.wrapping_add(x as u64))
}

/// Simple signature verification
pub fn verify_signature(message: &[u8], signature: &[u8], key: &[u8]) -> bool {
    // Simplified for example - real implementation would be more complex
    !message.is_empty() && !signature.is_empty() && !key.is_empty()
}

/// Simple encryption function
pub fn encrypt(data: &[u8], key: &[u8]) -> Vec<u8> {
    // Simplified for example - real implementation would use proper crypto
    data.iter().zip(key.iter().cycle())
        .map(|(&d, &k)| d ^ k)
        .collect()
}

/// Simple decryption function
pub fn decrypt(encrypted: &[u8], key: &[u8]) -> Vec<u8> {
    // Simplified for example - real implementation would use proper crypto
    encrypted.iter().zip(key.iter().cycle())
        .map(|(&e, &k)| e ^ k)
        .collect()
}

/// Cryptographic protocol example
pub fn sign_and_verify(message: &[u8], key: &[u8]) -> bool {
    let signature = vec![0u8; 32]; // Simplified signature
    verify_signature(message, &signature, key)
}

// Main function for testing
pub fn main() {
    let message = b"Hello, WebAssembly!";
    let key = b"secret_key_123";
    
    println!("Message hash: {}", simple_hash(message));
    println!("Signature valid: {}", verify_signature(message, b"sig", key));
    
    let encrypted = encrypt(message, key);
    let decrypted = decrypt(&encrypted, key);
    
    println!("Encryption works: {}", decrypted == message);
    println!("Protocol result: {}", sign_and_verify(message, key));
}