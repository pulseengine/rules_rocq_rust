#!/bin/bash

# Vendor Toolchains Script for rules_rocq_rust
# 
# This script helps set up a vendor directory for air-gap environments.
# It downloads all required toolchains and organizes them in the correct structure.

set -e

echo "rules_rocq_rust Vendor Toolchains Setup"
echo "======================================"
echo

# Configuration
DEFAULT_VENDOR_DIR="third_party/toolchains"
TOOLS=("rocq" "ocaml")
VERSIONS=("2025.01.0" "5.1.1")
PLATFORMS=("darwin_arm64" "darwin_amd64" "linux_amd64" "linux_arm64" "windows_amd64")

# Parse arguments
VENDOR_DIR="${VENDOR_DIR:-$DEFAULT_VENDOR_DIR}"
while getopts "d:" opt; do
  case $opt in
    d) VENDOR_DIR="$OPTARG" ;;
    *) echo "Usage: $0 [-d vendor_dir]" >&2 ; exit 1 ;;
  esac
done

echo "Vendor Directory: $VENDOR_DIR"
echo "Tools to vendor: ${TOOLS[@]}"
echo "Platforms: ${PLATFORMS[@]}"
echo

# Create vendor directory structure
mkdir -p "$VENDOR_DIR"
echo "Created vendor directory: $VENDOR_DIR"
echo

# Vendor each tool
for i in "${!TOOLS[@]}"; do
  TOOL="${TOOLS[$i]}"
  VERSION="${VERSIONS[$i]}"
  
  echo "Vendoring $TOOL $VERSION..."
  
  # Create tool/version directory structure
  TOOL_DIR="$VENDOR_DIR/$TOOL/$VERSION"
  mkdir -p "$TOOL_DIR"
  
  # Get checksums for this tool
  CHECKSUMS_FILE="checksums/tools/$TOOL.json"
  if [ ! -f "$CHECKSUMS_FILE" ]; then
    echo "Error: Checksums file not found: $CHECKSUMS_FILE"
    exit 1
  fi
  
  # Download for each platform
  for PLATFORM in "${PLATFORMS[@]}"; do
    echo "  Downloading for platform: $PLATFORM"
    
    # Extract download info from checksums file
    # This is a simplified version - in a real implementation, use jq or similar
    URL_SUFFIX=$(grep -A 10 "\"$PLATFORM\"" "$CHECKSUMS_FILE" | grep "url_suffix" | cut -d '"' -f 4)
    FILE_TYPE=$(grep -A 10 "\"$PLATFORM\"" "$CHECKSUMS_FILE" | grep "file_type" | cut -d '"' -f 4)
    
    if [ -z "$URL_SUFFIX" ]; then
      echo "    Skipping - no release for this platform"
      continue
    fi
    
    # Build download URL
    if [ "$TOOL" == "rocq" ]; then
      BASE_URL="https://github.com/rocq-prover/platform/releases/download/$VERSION"
    elif [ "$TOOL" == "ocaml" ]; then
      BASE_URL="https://github.com/ocaml/ocaml/releases/download/$VERSION"
    else
      echo "    Unknown tool: $TOOL"
      continue
    fi
    
    DOWNLOAD_URL="$BASE_URL/$URL_SUFFIX"
    FILENAME=$(basename "$URL_SUFFIX")
    
    echo "    Downloading: $DOWNLOAD_URL"
    
    # Download the file
    if command -v curl &> /dev/null; then
      curl -L -o "$TOOL_DIR/$FILENAME" "$DOWNLOAD_URL"
    elif command -v wget &> /dev/null; then
      wget -O "$TOOL_DIR/$FILENAME" "$DOWNLOAD_URL"
    else
      echo "    Error: Neither curl nor wget found"
      exit 1
    fi
    
    echo "    Downloaded: $TOOL_DIR/$FILENAME"
  done
  
  echo "  ✓ Completed $TOOL $VERSION"
  echo
done

echo "Vendor toolchains setup completed!"
echo
echo "To use the vendored toolchains:"
echo "1. Set environment variable: export BAZEL_ROCQ_OFFLINE=1"
echo "2. Or set custom vendor directory: export BAZEL_ROCQ_VENDOR_DIR=$VENDOR_DIR"
echo
echo "For enterprise deployment:"
echo "1. Copy $VENDOR_DIR to a shared location (NFS, etc.)"
echo "2. Set BAZEL_ROCQ_VENDOR_DIR to the shared path on all machines"
echo "3. All machines will use the shared toolchains without downloading"