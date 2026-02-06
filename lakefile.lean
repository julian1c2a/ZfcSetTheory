import Lake
open Lake DSL

package «ZfcSetTheory» where
  moreServerArgs := #["-DautoImplicit=false"]

@[default_target]
lean_lib «ZfcSetTheory» where
