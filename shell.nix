{ nixpkgs ? import <nixpkgs> {}, compiler ? "default" }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, base, containers, hashable, mtl, stdenv
      , template-haskell, unordered-containers, wl-pprint
      , parsec
      }:
      mkDerivation {
        pname = "query";
        version = "0.1.0.0";
        src = ./.;
        isLibrary = false;
        isExecutable = true;
        executableHaskellDepends = [
          base containers hashable mtl template-haskell unordered-containers
          wl-pprint
          parsec
        ];
        homepage = "https://github.com/githubuser/query#readme";
        description = "Language integrated query experiments";
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  drv = haskellPackages.callPackage f {};

in

  if pkgs.lib.inNixShell then drv.env else drv
