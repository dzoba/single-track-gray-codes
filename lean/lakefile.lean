import Lake
open Lake DSL

package stgc where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

@[default_target]
lean_lib STGC
