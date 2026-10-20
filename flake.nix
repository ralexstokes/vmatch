{
  description = "Rust development environment";

  inputs = {
    # Track nixpkgs and rust-overlay directly (rather than through rust-env's
    # lock) so `nix flake update` picks up new Rust releases; Verus pins an
    # exact rustc that is often newer than the template's lock.
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    rust-env = {
      url = "github:ralexstokes/rust-nix-template";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.rust-overlay.follows = "rust-overlay";
    };
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
      # Escape hatches (see the template repo's README):
      #   projectName = "my-project";
      #   extraShellPackages = pkgs: [ pkgs.mdbook ];
      #   extraBuildPackages = pkgs: [ pkgs.pkg-config ];
      #   extraChecks = pkgs: { };
      #   extraCiCommands = "cargo run --locked -p hello --example smoke";
    };
}
