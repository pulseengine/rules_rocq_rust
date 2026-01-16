# Debugging Guide for rules_rocq_rust

This guide provides comprehensive debugging information for rules_rocq_rust, helping you diagnose and resolve issues with toolchain setup, proof verification, and integration.

## Table of Contents

1. [Common Issues and Solutions](#common-issues-and-solutions)
2. [Toolchain Debugging](#toolchain-debugging)
3. [Proof Verification Debugging](#proof-verification-debugging)
4. [coq-of-rust Debugging](#coq-of-rust-debugging)
5. [Performance Debugging](#performance-debugging)
6. [Enterprise Deployment Debugging](#enterprise-deployment-debugging)
7. [Advanced Debugging Techniques](#advanced-debugging-techniques)

## Common Issues and Solutions

### Issue: Toolchain not found

**Symptoms:**
- `coq-of-rust binary not found`
- `Rocq compiler not found`
- Build fails with toolchain errors

**Solutions:**

1. **Check toolchain setup:**
   ```bash
   bazel info @rocq_toolchains//:all
   bazel info @coq_of_rust_toolchains//:all
   ```

2. **Verify MODULE.bazel:**
   ```bazel
   # Ensure you have proper toolchain setup
   rocq = use_extension("@rules_rocq_rust//rocq:extensions.bzl", "rocq")
   rocq.toolchain(version = "2025.01.0")
   use_repo(rocq, "rocq_toolchains")
   ```

3. **Check environment variables:**
   ```bash
   echo $BAZEL_ROCQ_OFFLINE
   echo $BAZEL_ROCQ_MIRROR
   ```

### Issue: Download failures

**Symptoms:**
- `Failed to download or verify tool`
- Network timeouts
- Checksum mismatches

**Solutions:**

1. **Use local test mode for development:**
   ```bash
   export BAZEL_ROCQ_LOCAL_TEST=1
   ./test_toolchain_repo/create_test_releases.py
   ```

2. **Check network connectivity:**
   ```bash
   curl -v https://github.com
   ```

3. **Use corporate mirror:**
   ```bash
   export BAZEL_ROCQ_MIRROR=https://your-mirror.com
   ```

### Issue: Proof verification failures

**Symptoms:**
- `Proof failed to verify`
- `Unresolved obligations`
- Coq compilation errors

**Solutions:**

1. **Check proof validity:**
   ```bash
   bazel test //examples/advanced_validation:test_all
   ```

2. **Review proof metrics:**
   ```bash
   bazel test //test:real_download_test --test_output=all
   ```

3. **Use detailed validation:**
   ```bazel
   rocq_proof_validation(
       name = "detailed_validation",
       srcs = ["your_proof.v"],
       validation_level = "comprehensive",
       coverage_analysis = True,
   )
   ```

## Toolchain Debugging

### Debugging Rocq Toolchain

**Enable verbose logging:**
```bash
bazel build //... --verbose_failures --sandbox_debug
```

**Check toolchain files:**
```bash
ls -la bazel-rules_rocq_rust/external/rocq_toolchains/
```

**Manual toolchain test:**
```bash
bazel run @rocq_toolchains//:coqc -- --version
```

### Debugging coq-of-rust Toolchain

**Check build logs:**
```bash
bazel build @coq_of_rust_toolchains//:all --sandbox_debug
```

**Test local build:**
```bash
cd third_party/coq_of_rust
cargo build --release
```

**Verify binary:**
```bash
./target/release/coq-of-rust --version
```

## Proof Verification Debugging

### Common Proof Issues

**Issue: Theorem not proven**
```coq
(* Check if you have: *)
Qed.  (* Missing this? *)

(* Or check for: *)
Admitted.  (* This means the proof is incomplete *)
```

**Issue: Type errors**
```coq
(* Check your definitions: *)
Definition my_def : Type := ...  (* Wrong type? *)

(* Use Compute to debug: *)
Compute my_def.
```

### Debugging Techniques

**Use Ltac debugging:**
```coq
(* Add this to see proof state: *)
Set Printing All.

(* Step through proofs: *)
Set Debug Ltac.
```

**Check proof coverage:**
```bash
bazel test //examples/advanced_validation:test_coverage
```

## coq-of-rust Debugging

### Translation Issues

**Issue: Rust syntax not supported**
```rust
// Check for unsupported features:
// - Async/await
// - Complex macros
// - Unsafe code
```

**Debug translation:**
```bash
# Test with simple Rust first:
cat > test.rs << 'EOF'
pub fn simple() -> i32 { 42 }
EOF

bazel run @coq_of_rust_toolchains//:coq-of-rust translate test.rs --output test.v
```

### Generated Coq Issues

**Issue: Invalid Coq syntax**
```coq
(* Check generated file: *)
Require Import CoqOfRust.Prelude.  (* Missing? *)
```

**Validate generated code:**
```bash
# Use Coq to check:
bazel run @rocq_toolchains//:coqc -compile test.v
```

## Performance Debugging

### Slow Builds

**Check build times:**
```bash
bazel build //... --profile=profile.log
bazel analyze-profile profile.log
```

**Optimize caching:**
```bash
# Clear cache if corrupted:
bazel clean --expunge

# Check cache stats:
bazel info used-heap-size
```

### Memory Issues

**Increase memory limits:**
```bash
bazel build //... --local_ram_resources=8192
```

**Monitor memory usage:**
```bash
# On macOS:
top -pid $(bazel info server_pid)

# On Linux:
htop -p $(bazel info server_pid)
```

## Enterprise Deployment Debugging

### Air-Gap Issues

**Verify offline setup:**
```bash
ls -la third_party/toolchains/
```

**Check vendor script:**
```bash
./scripts/vendor_toolchains.sh
./scripts/vendor_toolchains_secure.sh
```

### Mirror Issues

**Test mirror connectivity:**
```bash
curl -v $BAZEL_ROCQ_MIRROR
```

**Check mirror structure:**
```bash
# Should have:
# mirror.com/rocq/2025.01.0/darwin_arm64/file.dmg
# mirror.com/ocaml/5.1.1/linux_amd64/file.tar.gz
```

## Advanced Debugging Techniques

### Debugging Bazel Rules

**Check rule instantiation:**
```bash
bazel query 'kind(rocq_library, //...)'
bazel query 'kind(coq_of_rust_library, //...)'
```

**Inspect rule implementation:**
```bash
bazel build //:all --output_groups=debug_info
```

### Debugging Repository Rules

**Check repository instantiation:**
```bash
bazel info @rocq_toolchains//:all
bazel info @coq_of_rust_toolchains//:all
```

**Test repository rules:**
```bash
bazel fetch @rocq_toolchains//...
bazel fetch @coq_of_rust_toolchains//...
```

### Debugging with Strace

**Trace system calls:**
```bash
# On Linux/macOS:
strace -f -e trace=file bazel build //your_target

# Filter for toolchain access:
strace -f -e trace=open bazel build //your_target 2>&1 | grep toolchain
```

## Debugging Checklist

### Before Reporting Issues

- [ ] Check Bazel version: `bazel version`
- [ ] Verify toolchain setup in MODULE.bazel
- [ ] Test with simple examples first
- [ ] Check network connectivity if using downloads
- [ ] Review error messages carefully
- [ ] Search existing issues

### When Reporting Issues

1. **Provide reproduction steps**
2. **Include error messages** (full, not truncated)
3. **Specify environment** (OS, Bazel version, etc.)
4. **Share minimal reproduction** (small BUILD files)
5. **Describe expected vs actual behavior**

## Common Error Messages

### "coq-of-rust binary not found"
**Cause:** Toolchain not properly set up
**Solution:** Check MODULE.bazel and toolchain registration

### "No Rocq sources provided for validation"
**Cause:** Empty srcs in rocq_proof_validation
**Solution:** Provide valid .v files

### "Checksum verification failed"
**Cause:** Corrupted download or wrong checksum
**Solution:** Use BAZEL_ROCQ_LOCAL_TEST=1 for development

### "Unsupported archive format"
**Cause:** Unexpected file extension
**Solution:** Check toolchain URL patterns

## Performance Optimization Tips

### Faster Builds
```bash
# Use local execution:
bazel build //... --strategy=local

# Increase parallelism:
bazel build //... --local_cpu_resources=8

# Use disk cache:
bazel build //... --disk_cache=path/to/cache
```

### Memory Optimization
```bash
# Limit memory usage:
bazel build //... --local_ram_resources=4096

# Use smaller heap:
bazel build //... --host_jvm_args=-Xmx2g
```

## Security Debugging

### Verify Toolchain Integrity
```bash
# Check checksums:
sha256sum third_party/toolchains/*/*/*

# Verify downloads:
bazel run @rules_rocq_rust//test:real_download_test
```

### Check Environment Security
```bash
# Check for sensitive data:
grep -r "password\|secret\|token" .

# Verify file permissions:
find . -type f -perm -o+w
```

## Getting Help

### Community Resources
- GitHub Issues: Report bugs and feature requests
- Documentation: Read README.md and examples
- Stack Overflow: Use tag `bazel` + `coq`

### Commercial Support
For enterprise support and consulting:
- Contact: rules-rocq-rust@pulseengine.com
- Services: Toolchain setup, proof development, security audits

## Conclusion

This debugging guide should help you resolve most issues with rules_rocq_rust. If you encounter problems not covered here, please open a GitHub issue with detailed information about your setup and the error you're experiencing.

**Happy debugging!** Remember that formal verification is complex, and debugging is part of the process. The more you understand the tools, the better your proofs will be.