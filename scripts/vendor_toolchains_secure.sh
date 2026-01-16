#!/bin/bash

# Secure toolchain vendor script for rules_rocq_rust
# 
# This script downloads and verifies toolchains for air-gap/offline environments
# with enhanced security checks and validation.

set -euo pipefail

# Configuration
VENDOR_DIR="third_party/toolchains"
TEMP_DIR="$(mktemp -d)"
CHECKSUM_FILE="toolchain_checksums.txt"

# Security settings
VERIFY_CHECKSUMS=true
USE_HTTPS=true
TIMEOUT=60

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Security functions
echo_error() {
    echo -e "${RED}[ERROR]${NC} $1" >&2
}

echo_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1" >&2
}

echo_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

echo_info() {
    echo -e "${NC}[INFO]${NC} $1"
}

# Verify checksum function
verify_checksum() {
    local file="$1"
    local expected_checksum="$2"
    
    if [ ! -f "$file" ]; then
        echo_error "File not found: $file"
        return 1
    fi
    
    if command -v sha256sum >/dev/null 2>&1; then
        actual_checksum=$(sha256sum "$file" | awk '{print $1}')
    elif command -v shasum >/dev/null 2>&1; then
        actual_checksum=$(shasum -a 256 "$file" | awk '{print $1}')
    else
        echo_error "No checksum tool available (sha256sum or shasum)"
        return 1
    fi
    
    if [ "$actual_checksum" != "$expected_checksum" ]; then
        echo_error "Checksum mismatch for $file"
        echo_error "Expected: $expected_checksum"
        echo_error "Actual:   $actual_checksum"
        return 1
    fi
    
    echo_success "Checksum verified for $file"
    return 0
}

# Secure download function
secure_download() {
    local url="$1"
    local output="$2"
    
    echo_info "Downloading $url to $output..."
    
    if command -v curl >/dev/null 2>&1; then
        if $USE_HTTPS; then
            curl --silent --show-error --fail --location --timeout "$TIMEOUT" --output "$output" "$url"
        else
            curl --silent --show-error --fail --location --insecure --timeout "$TIMEOUT" --output "$output" "$url"
        fi
    elif command -v wget >/dev/null 2>&1; then
        if $USE_HTTPS; then
            wget --quiet --timeout="$TIMEOUT" --output-document="$output" "$url"
        else
            wget --quiet --timeout="$TIMEOUT" --no-check-certificate --output-document="$output" "$url"
        fi
    else
        echo_error "No download tool available (curl or wget)"
        return 1
    fi
    
    if [ ! -f "$output" ]; then
        echo_error "Download failed: $url"
        return 1
    fi
    
    echo_success "Downloaded $url"
    return 0
}

# Main vendor function
vendor_toolchain() {
    local tool_name="$1"
    local version="$2"
    local platform="$3"
    local url="$4"
    local checksum="$5"
    
    echo_info "Vending $tool_name $version for $platform..."
    
    # Create toolchain directory
    local tool_dir="$VENDOR_DIR/$tool_name/$version/$platform"
    mkdir -p "$tool_dir"
    
    # Download to temp file
    local temp_file="$TEMP_DIR/$tool_name-$version-$platform.$(basename "$url")"
    
    if ! secure_download "$url" "$temp_file"; then
        echo_error "Failed to download $tool_name $version for $platform"
        return 1
    fi
    
    # Verify checksum if provided
    if [ "$VERIFY_CHECKSUMS" = true ] && [ -n "$checksum" ]; then
        if ! verify_checksum "$temp_file" "$checksum"; then
            rm -f "$temp_file"
            echo_error "Checksum verification failed for $tool_name $version"
            return 1
        fi
    else
        echo_warning "Skipping checksum verification for $tool_name $version"
    fi
    
    # Move to final location
    mv "$temp_file" "$tool_dir/"
    
    echo_success "Vended $tool_name $version for $platform to $tool_dir"
    return 0
}

# Cleanup function
cleanup() {
    echo_info "Cleaning up temporary files..."
    rm -rf "$TEMP_DIR"
    echo_success "Cleanup completed"
}

# Main script
main() {
    echo_info "Starting secure toolchain vending..."
    
    # Check prerequisites
    if [ ! -d "$VENDOR_DIR" ]; then
        echo_info "Creating vendor directory: $VENDOR_DIR"
        mkdir -p "$VENDOR_DIR"
    fi
    
    # Create checksums file if it doesn't exist
    if [ ! -f "$CHECKSUM_FILE" ]; then
        echo_info "Creating checksums file: $CHECKSUM_FILE"
        touch "$CHECKSUM_FILE"
    fi
    
    # Read toolchain configurations
    # In a real implementation, this would read from a configuration file
    # For now, we'll use placeholder configurations
    
    echo_info "Setting up toolchain configurations..."
    
    # Example: Rocq Platform (placeholder URLs and checksums)
    declare -A rocq_configs=(
        ["darwin_arm64"]="https://github.com/rocq-prover/platform/releases/download/2025.01.0/Coq-Platform-release-2025.01.0-version.8.20.2025.01-MacOS-arm64.dmg|a1b2c3..."
        ["darwin_amd64"]="https://github.com/rocq-prover/platform/releases/download/2025.01.0/Coq-Platform-release-2025.01.0-version.8.20.2025.01-MacOS-x86_64.dmg|b2c3d4..."
        ["linux_amd64"]="https://github.com/rocq-prover/platform/releases/download/2025.01.0/Coq-Platform-release-2025.01.0-version.8.20.2025.01-Linux-x86_64.tar.gz|c3d4e5..."
        ["windows_amd64"]="https://github.com/rocq-prover/platform/releases/download/2025.01.0/Coq-Platform-release-2025.01.0-version.8.20.2025.01-Windows-x86_64.exe|d4e5f6..."
    )
    
    # Example: Test tool (real local files)
    declare -A test_configs=(
        ["darwin_arm64"]="test_releases/test-toolchain-1.0.0-darwin_arm64.tar.gz|4020550886e634fad5c6ee2214ca3b60b8fb1a38e22168f0c0e0b409d9751f99"
        ["darwin_amd64"]="test_releases/test-toolchain-1.0.0-darwin_amd64.tar.gz|fba2c7a4bdd8172097e2c80af94ab44730090c2310f72547df07c3d77139b5c1"
        ["linux_amd64"]="test_releases/test-toolchain-1.0.0-linux_amd64.tar.gz|c42a2f68e9a3edb980a9d0ba00ac30be4ed1f07beee2a65110e6358d2ac6ad66"
        ["windows_amd64"]="test_releases/test-toolchain-1.0.0-windows_amd64.zip|bc8e52ed7315b966df7be39c76a51e67bfde39104aab895f4a1823ba522203a4"
    )
    
    # Vendor test toolchain (uses real local files)
    echo_info "Vending test toolchain..."
    
    for platform in "${!test_configs[@]}"; do
        IFS='|' read -r url checksum <<< "${test_configs[$platform]}"
        
        # Check if file exists locally first
        local filename=$(basename "$url")
        if [ -f "$filename" ]; then
            echo_info "Using local file: $filename"
            cp "$filename" "test_releases/"
            url="test_releases/$filename"
        fi
        
        if ! vendor_toolchain "test_tool" "1.0.0" "$platform" "$url" "$checksum"; then
            echo_error "Failed to vendor test toolchain for $platform"
            # Continue with other platforms
        fi
    done
    
    # Note: In a real implementation, we would vendor actual toolchains
    # For security, this should be done in a controlled environment
    echo_warning "Real toolchain vending should be done in a secure, controlled environment"
    echo_warning "This script demonstrates the process but uses test data"
    
    # Update checksums file
    echo_info "Updating checksums file..."
    cat > "$CHECKSUM_FILE" << 'EOF'
# rules_rocq_rust Toolchain Checksums
# Generated by vendor_toolchains_secure.sh
# Format: tool_name|version|platform|checksum

# Test toolchain (real files)
test_tool|1.0.0|darwin_arm64|4020550886e634fad5c6ee2214ca3b60b8fb1a38e22168f0c0e0b409d9751f99
test_tool|1.0.0|darwin_amd64|fba2c7a4bdd8172097e2c80af94ab44730090c2310f72547df07c3d77139b5c1
test_tool|1.0.0|linux_amd64|c42a2f68e9a3edb980a9d0ba00ac30be4ed1f07beee2a65110e6358d2ac6ad66
test_tool|1.0.0|windows_amd64|bc8e52ed7315b966df7be39c76a51e67bfde39104aab895f4a1823ba522203a4

# Real toolchains would be added here in a secure environment
# rocq|2025.01.0|darwin_arm64|real_checksum_here
# coq_of_rust|0.5.0|linux_amd64|real_checksum_here
EOF

    echo_success "Toolchain vending completed"
    echo_info "Checksums saved to: $CHECKSUM_FILE"
    echo_info "Toolchains saved to: $VENDOR_DIR"
    
    # Security recommendations
    echo_info ""
    echo_info "Security Recommendations:"
    echo_info "1. Verify all checksums before using toolchains"
    echo_info "2. Store toolchains in secure, access-controlled location"
    echo_info "3. Monitor toolchain files for unexpected changes"
    echo_info "4. Use air-gap mode for production: BAZEL_ROCQ_OFFLINE=1"
    echo_info "5. Regularly update toolchains with security patches"
}

# Run main function with error handling
main "$@" 2>&1 | tee vendor_toolchains_secure.log

echo_info ""
echo_success "Secure toolchain vending script completed"
echo_info "Log saved to: vendor_toolchains_secure.log"

cleanup