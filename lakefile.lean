import Lake
open Lake DSL

package «lean-frozen-time» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

@[default_target]
lean_lib RelativeRest_OneFile_Certificate

lean_lib RelativeRest_Maxwell_Action

lean_lib RelativeRest_Maxwell_StressScaling

lean_lib RelativeRest_SynchronizationScope

lean_lib RelativeRest_FieldDerivedJet

lean_lib RelativeRest_ActionToJetBridge

lean_lib RelativeRest_ActionOddTensorJet

lean_lib RelativeRest_StrictVerification
