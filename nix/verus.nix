# Verus binary release, patched to run on NixOS.
#
# `rust_verify` links against `librustc_driver` from the exact rustc the
# release was built with, so `rustToolchain` must be that version (Verus
# records it in the release's version.json; keep rust-toolchain.toml in sync).
{
  lib,
  stdenv,
  fetchzip,
  autoPatchelfHook,
  rustToolchain,
}:
stdenv.mkDerivation rec {
  pname = "verus";
  version = "0.2026.10.18.7d82994";

  src = fetchzip {
    url = "https://github.com/verus-lang/verus/releases/download/release/${version}/verus-${version}-x86-linux.zip";
    hash = "sha256-3jXjAskHWK3GoX9HgGTdTDUveuazXcyHcMKxFD5gMUU=";
  };

  nativeBuildInputs = [ autoPatchelfHook ];
  buildInputs = [
    stdenv.cc.cc.lib
    rustToolchain
  ];

  # The driver locates its sibling files (vstd, builtin, z3) relative to its
  # own path, so keep the release tree intact and only link the entry points.
  installPhase = ''
    runHook preInstall
    mkdir -p $out/lib/verus $out/bin
    # The zip also carries cargo build leftovers and a release-maintenance
    # tool; none are needed at run time (and they would pull in openssl).
    rm -rf build deps incremental bump_crate_versions
    cp -r . $out/lib/verus
    for exe in verus cargo-verus z3; do
      ln -s $out/lib/verus/$exe $out/bin/$exe
    done
    runHook postInstall
  '';

  meta = {
    description = "Verified Rust for low-level systems code";
    homepage = "https://github.com/verus-lang/verus";
    platforms = [ "x86_64-linux" ];
  };
}
