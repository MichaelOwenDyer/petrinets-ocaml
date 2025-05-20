{
  description = "OCaml development shell";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";

  outputs = { nixpkgs, ... }:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forEachSupportedSystem = f: nixpkgs.lib.genAttrs supportedSystems (system: f {
        pkgs = nixpkgs.legacyPackages.${system};
      });
    in
    {
      devShells = forEachSupportedSystem ({ pkgs }: {
        default = pkgs.mkShell {
          nativeBuildInputs = with pkgs; [
            nixd
            nixfmt-rfc-style
          ];

          buildInputs = with pkgs; [
            ocaml
            dune_3
            ocamlPackages.findlib
            ocamlPackages.utop
            ocamlPackages.ocaml-lsp
            ocamlPackages.ocamlgraph
            ocamlPackages.ocamlformat
          ];

          shellHook = ''
            echo "OCaml dev shell ready."
          '';
        };
      });
    };
}
