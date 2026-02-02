{
  description = "Bazel rules for Rocq/Coq theorem proving and Rust formal verification";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    # Fenix provides Rust nightly with rustc-dev component
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # Pinned rocq-of-rust source
    rocq-of-rust-src = {
      url = "github:formal-land/rocq-of-rust/858907dbee116c51d7c6e87511bf5f92d6432ba4";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, fenix, rocq-of-rust-src }:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];

      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;

      # Get nixpkgs for a system
      pkgsFor = system: import nixpkgs {
        inherit system;
        overlays = [ fenix.overlays.default ];
      };

    in {
      packages = forAllSystems (system:
        let
          pkgs = pkgsFor system;

          # rocq-of-rust requires a specific nightly version (from rust-toolchain.toml)
          # Using fenix.toolchainOf to pin to exact date
          pinnedNightly = pkgs.fenix.toolchainOf {
            channel = "nightly";
            date = "2024-12-07";
            sha256 = "sha256-DS3fJ3/1FsdqEp85bDH5UsacGEk5RCBhB6AizDiT0TI=";
          };

          # Rust nightly with rustc-dev for rustc_private
          rustNightly = pkgs.fenix.combine [
            pinnedNightly.rustc
            pinnedNightly.cargo
            pinnedNightly.rust-src
            pinnedNightly.rustc-dev
            pinnedNightly.llvm-tools-preview
          ];

        in {
          # rocq-of-rust binary
          rocq-of-rust = let
            # This uses makeRustPlatform with our nightly toolchain
            rustPlatformNightly = pkgs.makeRustPlatform {
              cargo = rustNightly;
              rustc = rustNightly;
            };
            # Patch to use ROCQ_OF_RUST_SYSROOT env var instead of calling rustup
            patchedSrc = pkgs.stdenv.mkDerivation {
              name = "rocq-of-rust-patched-src";
              src = rocq-of-rust-src;
              phases = [ "unpackPhase" "patchPhase" "installPhase" ];
              patchPhase = ''
                # Patch sysroot_path to use env var instead of rustup
                substituteInPlace lib/src/bin/rocq-of-rust-rustc.rs \
                  --replace 'fn sysroot_path() -> String {' \
                'fn sysroot_path() -> String {
    if let Ok(sysroot) = std::env::var("ROCQ_OF_RUST_SYSROOT") {
        return sysroot;
    }
    // Original implementation follows:'
              '';
              installPhase = ''
                cp -r . $out
              '';
            };
          in rustPlatformNightly.buildRustPackage {
            pname = "rocq-of-rust";
            version = "0.1.0-858907d";

            src = patchedSrc;

            cargoLock = {
              lockFile = "${rocq-of-rust-src}/Cargo.lock";
              allowBuiltinFetchGit = true;
            };

            nativeBuildInputs = [
              pkgs.pkg-config
              pkgs.makeWrapper
            ];

            buildInputs = [
              pkgs.zlib
            ] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
              pkgs.libiconv
            ] ++ pkgs.lib.optionals pkgs.stdenv.isLinux [
              pkgs.openssl
            ];

            # Required for rustc_private crates
            RUSTC_BOOTSTRAP = 1;

            # Add rustc lib to library path for rustc_private linking
            preBuild = ''
              export LD_LIBRARY_PATH="${rustNightly}/lib:$LD_LIBRARY_PATH"
              export DYLD_LIBRARY_PATH="${rustNightly}/lib:$DYLD_LIBRARY_PATH"
              export LIBRARY_PATH="${rustNightly}/lib:$LIBRARY_PATH"
            '';

            # Skip tests during build
            doCheck = false;

            # Create sysroot symlink and wrap binaries
            postFixup = ''
              # Create a lib/rustlib symlink to make sysroot discovery work
              mkdir -p $out/lib
              ln -s ${rustNightly}/lib/rustlib $out/lib/rustlib

              # Wrap binaries to set library paths and sysroot
              for bin in $out/bin/*; do
                wrapProgram "$bin" \
                  --set DYLD_LIBRARY_PATH "${rustNightly}/lib" \
                  --set LD_LIBRARY_PATH "${rustNightly}/lib" \
                  --set ROCQ_OF_RUST_SYSROOT "${rustNightly}"
              done
            '';

            meta = with pkgs.lib; {
              description = "Formal verification of Rust programs by translation to Rocq";
              homepage = "https://github.com/formal-land/rocq-of-rust";
              license = licenses.mit;
              platforms = supportedSystems;
            };
          };

          default = self.packages.${system}.rocq-of-rust;
        });

      # Development shell with all tools
      devShells = forAllSystems (system:
        let
          pkgs = pkgsFor system;
          pinnedNightly = pkgs.fenix.toolchainOf {
            channel = "nightly";
            date = "2024-12-07";
            sha256 = "sha256-DS3fJ3/1FsdqEp85bDH5UsacGEk5RCBhB6AizDiT0TI=";
          };
          rustNightly = pkgs.fenix.combine [
            pinnedNightly.rustc
            pinnedNightly.cargo
            pinnedNightly.rust-src
            pinnedNightly.rustc-dev
            pinnedNightly.rust-analyzer
          ];
        in {
          default = pkgs.mkShell {
            nativeBuildInputs = [
              rustNightly
              pkgs.pkg-config
              pkgs.bazel_7
            ];

            RUSTC_BOOTSTRAP = 1;
          };
        });
    };
}
