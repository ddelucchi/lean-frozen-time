import Lake
open Lake DSL

package «lean-frozen-time» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

lean_lib RelativeRest_OneFile_Certificate
lean_lib RelativeRest_DeepPass2
lean_lib RelativeRest_DeepPass3

@[default_target]
lean_lib RelativeRest_DeepPass4
