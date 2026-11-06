{
  description = "Development environment for the OrlikSolomon Lean formalization";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      forAllSystems = nixpkgs.lib.genAttrs [ "x86_64-linux" "aarch64-linux" ];
    in {
      devShells = forAllSystems (system:
        let pkgs = nixpkgs.legacyPackages.${system};
        in {
          # `mkShell` provides `cc`, which Verso's native dependency MD4Lean needs.
          default = pkgs.mkShell {
            packages = [ pkgs.elan pkgs.gh pkgs.git ];
          };
        });
    };
}
