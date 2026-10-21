{
  description = "Rust development environment";

  inputs = {
    rust-env.url = "github:ralexstokes/rust-nix-template";
  };

  outputs =
    { self, rust-env, ... }:
    rust-env.lib.mkRustProject {
      src = ./.;
      # The check sandbox keeps only Cargo sources by default; anything else a
      # check reads (configs, docs pulled in by include_str!) must be listed
      # here or `nix flake check` silently runs without it.
      extraSourceFilter =
        path: type: builtins.match ".*/\\.config/nextest\\.toml" (toString path) != null;
      # Verus is pinned to one exact rustc, which rust-toolchain.toml selects.
      extraShellPackages = pkgs: [
        (pkgs.callPackage ./nix/verus.nix {
          rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
        })
      ];
      # Check the proofs. Crane vendors Cargo.lock (vstd included), so this
      # runs offline in the sandbox. `--no-cheating` rejects assume, admit,
      # external_body and assume_specification anywhere in the core crate.
      # Mirrored by `just verify`.
      extraChecks =
        {
          pkgs,
          craneLibStable,
          commonArgs,
          rustToolchain,
          ...
        }:
        let
          # The verus driver finds rustc through rustup, so give it a rustup
          # home holding just the pinned toolchain (as the devshell does).
          channel = (builtins.fromTOML (builtins.readFile ./rust-toolchain.toml)).toolchain.channel;
          host = pkgs.stdenv.hostPlatform.rust.rustcTarget;
          rustupHome = pkgs.runCommandLocal "vmatch-verus-rustup-home" { } ''
            mkdir -p $out/toolchains $out/update-hashes
            ln -s ${rustToolchain} $out/toolchains/${channel}-${host}
            printf 'version = "12"\n\n[overrides]\n' > $out/settings.toml
          '';
        in
        {
          verus = craneLibStable.mkCargoDerivation (
            commonArgs
            // {
              pname = "vmatch-verus";
              cargoArtifacts = null;
              nativeBuildInputs = [
                pkgs.rustup
                (pkgs.callPackage ./nix/verus.nix { inherit rustToolchain; })
              ];
              RUSTUP_HOME = rustupHome;
              RUSTUP_TOOLCHAIN = channel;
              buildPhaseCargoCommand = ''
                cd core
                cargo verus focus -- --no-cheating
              '';
              doInstallCargoArtifacts = false;
            }
          );
        };
      # Escape hatches (see the template repo's README):
      #   projectName = "my-project";
      #   extraCiCommands = "cargo run --locked -p hello --example smoke";
    };
}
