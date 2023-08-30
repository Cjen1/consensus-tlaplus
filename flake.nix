{ 
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";

    apalache-release = {
      url = "https://github.com/informalsystems/apalache/releases/download/v0.41.3/apalache.zip";
      flake = false;
      type = "tarball";
    };

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
    apalache = import ./apalache.nix {inherit pkgs inputs;};
  in {
    devShell = pkgs.mkShell {
      buildInputs = [
        #pkgs.tlaplus
        apalache
      ];
    };
  });
}
