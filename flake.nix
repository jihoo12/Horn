{
  description = "Horn: a small checker for many-sorted Horn derivation certificates";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/b6018f87da91d19d0ab4cf979885689b469cdd41";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      eachSystem = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in {
      packages = eachSystem (pkgs: {
        default = pkgs.rustPlatform.buildRustPackage {
          pname = "horn";
          version = "0.3.0";
          src = self;
          cargoLock.lockFile = ./Cargo.lock;
        };
      });

      devShells = eachSystem (pkgs: {
        default = pkgs.mkShell {
          packages = with pkgs; [ cargo rustc rustfmt clippy agda ];
        };
      });

      checks = eachSystem (pkgs: {
        rust = self.packages.${pkgs.stdenv.hostPlatform.system}.default;
        # The soundness proof uses no libraries; --safe rejects postulates.
        agda = pkgs.runCommand "horn-agda-soundness" { nativeBuildInputs = [ pkgs.agda ]; } ''
          cp -R ${self}/agda agda
          chmod -R u+w agda
          agda --safe --no-libraries -i agda agda/Soundness.agda
          agda --safe --no-libraries -i agda agda/Schematic.agda
          touch "$out"
        '';
      });
    };
}
