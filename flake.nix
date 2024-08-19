{ 
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";

    apalache-release = {
      url = "https://github.com/informalsystems/apalache/releases/download/v0.44.11/apalache.zip";
      flake = false;
      type = "tarball";
    };
  };

  outputs = {self, nixpkgs, flake-utils, ... }@inputs:
  flake-utils.lib.eachDefaultSystem (system:
  let 
    pkgs = import nixpkgs {
      inherit system;
    };
    apalache = pkgs.stdenv.mkDerivation {
      name = "apalache";
      src = inputs.apalache-release;

      buildInputs = [pkgs.makeWrapper];

      installPhase = ''
        mkdir -p $out
        cp -r lib $out/lib

        mkdir -p $out/bin
        cat > $out/bin/apalache-mc <<- EOM
        #!${pkgs.bash}/bin/bash
        exec ${pkgs.jre}/bin/java -Xmx100G -jar "$out/lib/apalache.jar" "\$@"
        EOM
        chmod +x $out/bin/apalache-mc
      '';

      postFixup = ''
        wrapProgram $out/bin/apalache-mc \
          --set PATH ${pkgs.lib.makeBinPath [
              pkgs.gcc12
              pkgs.z3
            ]}
      '';
    };
  in {
    devShell = pkgs.mkShell {
      buildInputs = [
        pkgs.tlaplus
        apalache
      ];
    };
  });
}
