{
  description = "Epicycles Flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    treefmt-nix.url = "github:numtide/treefmt-nix";
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      imports = [ inputs.treefmt-nix.flakeModule ];

      perSystem =
        { pkgs, ... }:
        let
          freetype2 = pkgs.fetchFromGitHub {
            owner = "dagit";
            repo = "freetype2";
            rev = "cabalization";
            hash = "sha256-KR/EklKbCfocQj7/fkiY80D0wZ2ZrgckmGuZN08qWMI=";
          };

          hp = pkgs.haskell.packages.ghc912.extend (
            final: prev: {

              # nixpkgs unstable moment :(
              # if you have trouble running this, it _should_ work fine on nixpkgs-25.11
              # i raised it to unstable to update to the most recent lean version to fix some version mismatch
              # with a linter that never ended up being used (perhaps a poor use of my time in retrospect)
              dear-imgui = pkgs.haskell.lib.doJailbreak (pkgs.haskell.lib.markUnbroken prev.dear-imgui); # seems fine to me
              colonnade = pkgs.haskell.lib.dontCheck (pkgs.haskell.lib.markUnbroken prev.colonnade);
              freetype2 = pkgs.haskell.lib.dontCheck (
                pkgs.haskell.lib.doJailbreak (final.callCabal2nix "freetype2" "${freetype2}" { })
              );
              storable-offset = pkgs.haskell.lib.doJailbreak (pkgs.haskell.lib.markUnbroken prev.storable-offset);
              th-desugar = pkgs.haskell.lib.doJailbreak prev.th-desugar;
              singletons = final.callHackage "singletons" "3.0.4" { };
              singletons-base = pkgs.haskell.lib.dontCheck (
                pkgs.haskell.lib.doJailbreak (final.callHackage "singletons-base" "3.5" { })
              );
              singletons-th = pkgs.haskell.lib.doJailbreak prev.singletons-th;
              singletons-base-code-generator = pkgs.haskell.lib.markUnbroken prev.singletons-base-code-generator;
              gl = prev.gl.overrideAttrs (oldAttrs: {
                meta = (oldAttrs.meta or { }) // {
                  # marked as bad on aarch64-darwin but it seems fine
                  badPlatforms = [ ];
                  platforms = (oldAttrs.meta.platforms or [ ]) ++ [ "aarch64-darwin" ];
                };
              });
            }
          );

          project = pkgs.haskell.lib.overrideCabal (hp.callCabal2nix "vector-dsl" ./. { }) (drv: {
            extraLibraries = (drv.extraLibraries or [ ]) ++ [ pkgs.SDL2 ];
            buildTools = (drv.buildTools or [ ]) ++ [ pkgs.pkg-config ];
          });

          pythonEnv = pkgs.python3.withPackages (p: [
            p.fonttools
            p.pandas
          ]);

          texEnv = pkgs.texlive.combine {
            inherit (pkgs.texlive)
              scheme-medium
              datetime
              tracklang
              ifoddpage
              relsize
              lipsum
              todonotes
              fmtcount
              minted
              upquote
              tabularray
              ninecolors
              mathpartir
              natbib
              cleveref
              newunicodechar
              ;
          };

        in
        {
          packages.default = project;

          devShells.default = hp.shellFor {
            packages = p: [ project ];

            nativeBuildInputs =
              (with hp; [
                cabal-install
                haskell-language-server
                hlint
                fourmolu
                stan
              ])
              ++ (with pkgs; [
                texlab

                pythonEnv
                texEnv
                cm_unicode

                pkg-config

                lean4
                elan

                typst
              ]);

            shellHook = ''
              export PYTHONPATH="${pythonEnv}/${pythonEnv.sitePackages}"

              export OSFONTDIR="${pkgs.cm_unicode}/share/fonts/opentype//"
            '';
          };

          treefmt = {
            projectRootFile = "flake.nix";
            programs.nixfmt.enable = true;
            programs.cabal-fmt.enable = true;
            programs.fourmolu.enable = true;
            programs.hlint.enable = true;
            programs.latexindent.enable = true;
          };
        };

    };
  nixConfig = {
    extra-substituters = [ "https://bristermittenmasters.cachix.org" ];
    extra-trusted-public-keys = [
      "bristermittenmasters.cachix.org-1:eLYHPB8cVJO8dOCs77ISXVPhtQ+QZHIo4aeWGMo0XOk="
    ];
  };
}
