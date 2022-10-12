{ pkgs ? import <nixpkgs> { }
}:

pkgs.haskellPackages.developPackage
{
  returnShellEnv = true;
  root = ./.;
  modifier = with pkgs; with haskellPackages; drv:
    haskell.lib.overrideCabal drv (attrs: {
      buildTools = (attrs.buildTools or [ ]) ++ [
        cabal-install
      ];
    });
}