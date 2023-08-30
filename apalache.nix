{pkgs, inputs, ...} :
pkgs.stdenv.mkDerivation {
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
}
#let
#  version = "dev";
#  patch = ''
#    diff --git a/build.sbt b/build.sbt
#    index 4f9150ee5..87244fb5b 100644
#    --- a/build.sbt
#    +++ b/build.sbt
#    @@ -190,7 +190,7 @@ lazy val tool = (project in file("mod-tool"))
#           // See https://github.com/sbt/sbt-buildinfo
#           buildInfoPackage := "apalache",
#           buildInfoKeys := {
#    -        val build = Process("git describe --tags --always").!!.trim
#    +        val build = "${version}"
#             Seq[BuildInfoKey](
#                 BuildInfoKey.map(version) { case (k, v) =>
#                   if (isSnapshot.value) (k -> build) else (k -> v)
#  '';
#in inputs.sbt.lib.mkSbtDerivation {
#  inherit pkgs;
#  pname = "apalache";
#  inherit version;
#
#  depsSha256 = "sha256-LAFPHzhN4Wi5E1fT1cr0snFqpzj1fUfJfPJKNakOo5I=";
#
#  src = inputs.apalache-src;
#
#  patches = [(builtins.toFile "diff.patch" patch)];
#
#  buildPhase = ''
#  make dist
#  '';
#
#  installPhase = ''
#  mkdir -p $out/lib
#  mkdir -p $out/bin
#  mkdir -p target/out
#
#  tar xf target/universal/apalache.tgz -C target/out
#
#  cp -r target/out/apalache/lib/apalache.jar $out/lib/apalache.jar
#
#  cat > $out/bin/apalache-mc <<- EOM
#  #!${pkgs.bash}/bin/bash
#  exec ${pkgs.jre}/bin/java -Xmx100G -Djava.library.path=${pkgs.glibc} -jar "$out/lib/apalache.jar" "\$@"
#  EOM
#
#  chmod +x $out/bin/apalache-mc
#  '';
# }
