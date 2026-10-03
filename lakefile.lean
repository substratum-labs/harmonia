import Lake
open Lake DSL

package "harmonia" where
  version := v!"0.1.0"
  keywords := #["distributed-systems", "formal-methods", "lean4", "consensus"]

lean_lib «Harmonia» where
  -- Root library for Harmonia formal specification and verification

@[default_target]
lean_exe "harmonia" where
  root := `Main
