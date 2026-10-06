import Lake
open Lake DSL

package «lean-frozen-time» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

lean_lib RelativeRest_OneFile_Certificate
lean_lib RelativeRest_DeepPass2
lean_lib RelativeRest_DeepPass3
lean_lib RelativeRest_DeepPass4
lean_lib RelativeRest_DeepPass5
lean_lib RelativeRest_DeepPass6
lean_lib RelativeRest_DeepPass7
lean_lib RelativeRest_DeepPass8
lean_lib RelativeRest_DeepPass9
lean_lib RelativeRest_DeepPass10
lean_lib RelativeRest_DeepPass11
lean_lib RelativeRest_DeepPass12
lean_lib RelativeRest_DeepPass13
lean_lib RelativeRest_DeepPass14
lean_lib RelativeRest_DeepPass15
lean_lib RelativeRest_DeepPass16
lean_lib RelativeRest_DeepPass17
lean_lib RelativeRest_DeepPass18
lean_lib RelativeRest_DeepPass19

@[default_target]
lean_lib RelativeRest_Audit
