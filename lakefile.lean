import Lake
open Lake DSL

package «ZfcSetTheory» where
  moreServerArgs := #["-DautoImplicit=false"]

require peanolib from git
  "https://github.com/julian1c2a/Peano" @ "master"


@[default_target]
lean_lib «ZFC» where
