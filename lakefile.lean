import Lake
open Lake DSL

package «ComputableReals» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

@[default_target]
lean_lib «ComputableReals» where
  -- Computable real and complex arithmetic: executable engine, specification
  -- model, and the soundness bridge connecting them.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"
