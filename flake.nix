{
  inputs = {
    nixpkgs.url = github:nixos/nixpkgs;
    flake-utils.url = github:numtide/flake-utils;
    apalache-src.flake = false;
    apalache-src.url = github:informalsystems/apalache;
    sbt-derivation.url = github:zaninime/sbt-derivation;
  };

  outputs = { self, nixpkgs, flake-utils, apalache-src, sbt-derivation}:
  flake-utils.lib.eachDefaultSystem (system:
  let 
    pkgs = import nixpkgs {
      inherit system;
      overlays = [
        sbt-derivation.overlay
      ];
    };
    apalache = let
      version = "v0.25.3";
      patch = ''
        diff --git a/build.sbt b/build.sbt
        index 4f9150ee5..87244fb5b 100644
        --- a/build.sbt
        +++ b/build.sbt
        @@ -190,7 +190,7 @@ lazy val tool = (project in file("mod-tool"))
               // See https://github.com/sbt/sbt-buildinfo
               buildInfoPackage := "apalache",
               buildInfoKeys := {
        -        val build = Process("git describe --tags --always").!!.trim
        +        val build = "${version}"
                 Seq[BuildInfoKey](
                     BuildInfoKey.map(version) { case (k, v) =>
                       if (isSnapshot.value) (k -> build) else (k -> v)
      '';

    in pkgs.sbt.mkDerivation {
      pname = "apalache";
      inherit version;

      depsSha256 = "sha256-9wGlIFmvKW4N8NQqhOlxjhl48JptHCSI8F8EFF9mYrw=";

      src = apalache-src;

      patches = [
        (builtins.toFile "diff.patch" patch)
        ];

        buildPhase = ''
                    make dist
        '';

        installPhase = ''
                    mkdir -p $out/lib
                    mkdir -p $out/bin
                    mkdir -p target/out

                    tar xf target/universal/apalache.tgz -C target/out

                    cp -r target/out/apalache/lib/apalache.jar $out/lib/apalache.jar

                    cat > $out/bin/apalache-mc <<- EOM
                    #!${pkgs.bash}/bin/bash
                    exec ${pkgs.jre}/bin/java -Xmx4096m -jar "$out/lib/apalache.jar" "\$@"
                    EOM

                    chmod +x $out/bin/apalache-mc
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
