# SPDX-License-Identifier: MPL-2.0
{
  description = "tropical-resource-typing — Lean 4 + Isabelle/HOL proofs of tropical/resource semirings";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (s: f nixpkgs.legacyPackages.${s});
    in {
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          # `elan` manages the Lean toolchain pinned in ./lean-toolchain
          # (leanprover/lean4:v4.13.0); `just` is the task runner. Isabelle
          # is installed separately for the *.thy session.
          packages = [ pkgs.elan pkgs.just ];
        };
      });
    };
}
