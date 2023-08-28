{ 
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";

    #apalache-release = {
    #  url = "https://github.com/informalsystems/apalache/releases/download/v0.41.3/apalache.zip";
    #  flake = false;
    #  type = "tarball";
    #};

    apalache-src = {
      url = "github:informalsystems/apalache";
      flake = false;
    };

    sbt.url = "github:zaninime/sbt-derivation";
  };

  outputs = {self, nixpkgs, flake-utils, ... }@inputs:
  flake-utils.lib.eachDefaultSystem (system:
  let 
    pkgs = import nixpkgs {
      inherit system;
    };
    #apalache = pkgs.stdenv.mkDerivation {
    #  name = "apalache";
    #  src = apalache-release;

    #  buildInputs = [pkgs.makeWrapper];

    #  propogatedBuildInputs = [pkgs.z3];

    #  installPhase = ''
    #    mkdir -p $out
    #    cp -r lib $out/lib

    #    mkdir -p $out/bin
    #    cat > $out/bin/apalache-mc <<- EOM
    #    #!${pkgs.bash}/bin/bash
    #    exec ${pkgs.jre}/bin/java -Xmx100G -jar "$out/lib/apalache.jar" "\$@"
    #    EOM
    #    chmod +x $out/bin/apalache-mc
    #  '';
    #};
    apalache = import ./apalache.nix {inherit pkgs inputs;};
  in {
    devShell = pkgs.mkShell {
      buildInputs = [
        pkgs.tlaplus
        apalache
      ];
    };
  });
}
