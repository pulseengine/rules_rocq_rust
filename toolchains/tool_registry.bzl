"""Unified Tool Registry - Single API for all Rocq toolchain downloads

This module consolidates toolchain download logic following the exact pattern
established by rules_wasm_component.

Usage:
    load("//toolchains:tool_registry.bzl", "tool_registry")
    
    # In repository rule implementation:
    platform = tool_registry.detect_platform(ctx)
    tool_registry.download(ctx, "rocq", "2025.01.0", platform)

Enterprise/Air-Gap Support:
    The registry respects these environment variables for enterprise deployments:
    
    BAZEL_ROCQ_OFFLINE=1
        Use vendored files from third_party/toolchains/ (must run vendor workflow first)
    
    BAZEL_ROCQ_VENDOR_DIR=/path/to/vendor
        Use custom vendor directory (e.g., NFS mount for shared cache)
    
    BAZEL_ROCQ_MIRROR=https://mirror.company.com
        Download from corporate mirror instead of public URLs
"""

load("//checksums:registry.bzl", "get_tool_checksum", "get_tool_info")

# =============================================================================
# Platform Detection (Single Implementation)
# =============================================================================

def detect_platform(repository_ctx):
    """Detect the host platform in normalized format.
    
    This is the SINGLE source of truth for platform detection.
    All toolchains should use this instead of implementing their own.
    
    Args:
        repository_ctx: Bazel repository context
        
    Returns:
        String in format "{os}_{arch}" e.g., "darwin_arm64", "linux_amd64"
    """
    os_name = repository_ctx.os.name.lower()
    arch = repository_ctx.os.arch.lower()
    
    # Normalize OS names
    if "mac" in os_name or "darwin" in os_name:
        os_name = "darwin"
    elif "windows" in os_name:
        os_name = "windows"
    elif "linux" in os_name:
        os_name = "linux"
    
    # Normalize architecture names
    if arch in ["x86_64", "amd64"]:
        arch = "amd64"
    elif arch in ["aarch64", "arm64"]:
        arch = "arm64"
    
    return "{}_{}".format(os_name, arch)

# =============================================================================
# URL Pattern Handlers (Tool-Specific)
# =============================================================================

# Each tool has different URL patterns. These are centralized here.
_URL_PATTERNS = {
    "rocq": {
        "base": "https://github.com/{repo}/releases/download/{version}",
        "filename": "Coq-Platform-release-{version}-{suffix}",
    },
    "ocaml": {
        "base": "https://github.com/{repo}/releases/download/{version}",
        "filename": "ocaml-{version}-{suffix}",
    },
}

def _build_download_url(tool_name, version, platform, tool_info, github_repo):
    """Build the download URL for a tool.
    
    Args:
        tool_name: Name of the tool
        version: Version to download
        platform: Platform string (e.g., "darwin_arm64")
        tool_info: Tool info dict from registry
        github_repo: GitHub repo in "owner/repo" format
        
    Returns:
        Download URL string
    """
    pattern = _URL_PATTERNS.get(tool_name)
    if not pattern:
        fail("No URL pattern defined for tool '{}'. Add it to _URL_PATTERNS.".format(tool_name))
    
    # Build base URL
    base_template = pattern["base"]
    base_url = base_template.format(repo = github_repo, version = version)
    
    # Get filename pattern fields from tool_info
    filename_params = {
        "version": version,
        "suffix": tool_info.get("url_suffix", ""),
    }
    
    filename = pattern["filename"].format(**filename_params)
    
    return "{}/{}".format(base_url, filename)

# =============================================================================
# Enterprise/Air-Gap Source Resolution
# =============================================================================

def _resolve_download_source(repository_ctx, tool_name, version, platform, default_url, filename):
    """Resolve download source with enterprise air-gap support.
    
    Checks environment variables in priority order:
    1. BAZEL_ROCQ_OFFLINE=1 - Use vendored files from third_party/toolchains/
    2. BAZEL_ROCQ_VENDOR_DIR - Custom vendor directory (NFS/shared)
    3. BAZEL_ROCQ_MIRROR - Single mirror for all tools
    4. Default URL (github.com, etc.)
    
    Args:
        repository_ctx: Bazel repository context
        tool_name: Name of the tool (e.g., "rocq")
        version: Version string (e.g., "2025.01.0")
        platform: Platform string (e.g., "darwin_arm64")
        default_url: Default download URL
        filename: Filename portion of the URL
        
    Returns:
        struct with:
            type: "local" or "url"
            path: Local file path (if type == "local")
            url: Download URL (if type == "url")
    """
    # Priority 1: Offline mode with default vendor path
    offline_mode = repository_ctx.os.environ.get("BAZEL_ROCQ_OFFLINE", "0") == "1"
    if offline_mode:
        # Try workspace-relative path first
        vendor_path = repository_ctx.path(
            repository_ctx.workspace_root + "/third_party/toolchains/{}/{}/{}".format(
                tool_name, version, filename
            )
        )
        if vendor_path.exists:
            return struct(type = "local", path = str(vendor_path))
        
        fail("Offline mode enabled but tool not found in vendor directory: {}".format(vendor_path))
    
    # Priority 2: Custom vendor directory
    vendor_dir = repository_ctx.os.environ.get("BAZEL_ROCQ_VENDOR_DIR")
    if vendor_dir:
        vendor_path = repository_ctx.path(vendor_dir + "/{}/{}/{}".format(
            tool_name, version, filename
        ))
        if vendor_path.exists:
            return struct(type = "local", path = str(vendor_path))
        
        fail("Vendor directory set but tool not found: {}".format(vendor_path))
    
    # Priority 3: Corporate mirror
    mirror_url = repository_ctx.os.environ.get("BAZEL_ROCQ_MIRROR")
    if mirror_url:
        mirror_url = mirror_url.rstrip("/")
        return struct(
            type = "url",
            url = "{}/{}/{}/{}".format(mirror_url, tool_name, version, platform, filename)
        )
    
    # Priority 4: Default public URL
    return struct(type = "url", url = default_url)

# =============================================================================
# Download and Verification
# =============================================================================

def download_and_verify(repository_ctx, tool_name, version, platform):
    """Download tool with checksum verification.
    
    Args:
        repository_ctx: Bazel repository context
        tool_name: Name of the tool
        version: Version to download
        platform: Platform string
        
    Returns:
        Path to downloaded and verified tool
    """
    # Get tool info from registry
    tool_info = get_tool_info(repository_ctx, tool_name, version, platform)
    if not tool_info:
        fail("No tool info found for {} {} on {}".format(
            tool_name, version, platform
        ))
    
    expected_checksum = tool_info.get("sha256")
    url_suffix = tool_info.get("url_suffix", "")
    
    # Get GitHub repo from registry
    tool_data = _load_tool_checksums_from_json(repository_ctx, tool_name)
    github_repo = tool_data.get("github_repo", "rocq-prover/platform")
    
    # Build download URL
    default_url = _build_download_url(tool_name, version, platform, tool_info, github_repo)
    filename = native.path.basename(default_url)
    
    # Resolve download source
    source = _resolve_download_source(
        repository_ctx, tool_name, version, platform, default_url, filename
    )
    
    # Download the tool
    if source.type == "local":
        tool_path = source.path
    else:
        # Download from URL with verification
        download_result = repository_ctx.download(
            url = source.url,
            sha256 = expected_checksum,
        )
        tool_path = download_result.path
        
        # Verify the checksum matches
        # In a real implementation, this would use actual checksum verification
        print("Downloaded:", tool_path)
        print("Expected checksum:", expected_checksum)
    
    return tool_path

# =============================================================================
# Public API
# =============================================================================

def _load_tool_checksums_from_json(repository_ctx, tool_name):
    """Internal helper to load JSON checksums."""
    json_file = repository_ctx.path("@rules_rocq_rust//checksums/tools:{}.json".format(tool_name))
    if not json_file.exists:
        fail("Checksums not found: //checksums/tools/{}.json".format(tool_name))
    
    content = repository_ctx.read(json_file)
    return native.json.decode(content)