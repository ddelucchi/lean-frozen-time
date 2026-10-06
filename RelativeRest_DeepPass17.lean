import RelativeRest_DeepPass16

/-!
# Relative Rest: deep forced pass 17

Close the local/global clock bridge canonically.

The integrated characteristic response now produces its own clock quotient, and the local metric
normalization produces its own clock quotient.  Since each quotient carries a forced nonzero
covector to R, their identification is the unique covector-preserving linear equivalence obtained
by passing through the common real clock coordinate.

No basis, spanning hypothesis, or independently chosen unit vector is supplied.
-/

noncomputable section

open Function Set

namespace RelativeRest

section ForcedGlobalLocalClockBridge

variable {P K V : Type*}
  [AddCommGroup P] [Module ℝ P]
  [AddCommGroup K] [Module ℝ K]
  [AddCommGroup V] [Module ℝ V]

variable (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- Canonical identification between the integrated characteristic clock quotient and the local
metric clock quotient. -/
noncomputable def forcedGlobalLocalClockEquiv
    (D : CharacteristicResponseData (P:=P) (K:=K))
    (u : V) (omega : ℝ)
    (homega : omega ≠ 0)
    (hu : B u u = -1) :
    (LinearMap.range D.beta ⧸
        LinearMap.ker (characteristicLambda D)) ≃ₗ[ℝ]
      (V ⧸ LinearMap.ker (metricClockCovector B u omega)) :=
  canonicalClockLineEquiv
    (characteristicLambda D)
    (characteristicLambda_nonzero D)
    (metricClockCovector B u omega)
    (metricClockCovector_nonzero B u omega homega hu)

/-- The bridge preserves the two independently forced clock covectors exactly. -/
theorem forcedGlobalLocalClockEquiv_preserves_covector
    (D : CharacteristicResponseData (P:=P) (K:=K))
    (u : V) (omega : ℝ)
    (homega : omega ≠ 0)
    (hu : B u u = -1)
    (x : LinearMap.range D.beta ⧸
      LinearMap.ker (characteristicLambda D)) :
    canonicalClockCovector
        (metricClockCovector B u omega)
        (metricClockCovector_nonzero B u omega homega hu)
        (forcedGlobalLocalClockEquiv B D u omega homega hu x) =
      canonicalClockCovector
        (characteristicLambda D)
        (characteristicLambda_nonzero D)
        x := by
  exact canonicalClockLineEquiv_preserves_covector
    (characteristicLambda D)
    (characteristicLambda_nonzero D)
    (metricClockCovector B u omega)
    (metricClockCovector_nonzero B u omega homega hu)
    x

/-- The unique positive normalized global clock element is sent to the unique normalized local
clock element. -/
@[simp] theorem forcedGlobalLocalClockEquiv_maps_unit
    (D : CharacteristicResponseData (P:=P) (K:=K))
    (u : V) (omega : ℝ)
    (homega : omega ≠ 0)
    (hu : B u u = -1) :
    forcedGlobalLocalClockEquiv B D u omega homega hu
        (canonicalClockUnit
          (characteristicLambda D)
          (characteristicLambda_nonzero D)) =
      canonicalClockUnit
        (metricClockCovector B u omega)
        (metricClockCovector_nonzero B u omega homega hu) := by
  exact canonicalClockLineEquiv_maps_unit
    (characteristicLambda D)
    (characteristicLambda_nonzero D)
    (metricClockCovector B u omega)
    (metricClockCovector_nonzero B u omega homega hu)

/-- Any linear map preserving the two forced covectors is this bridge.  Hence one-dimensionality
leaves no residual identification freedom. -/
theorem forcedGlobalLocalClockMap_unique
    (D : CharacteristicResponseData (P:=P) (K:=K))
    (u : V) (omega : ℝ)
    (homega : omega ≠ 0)
    (hu : B u u = -1)
    (I :
      (LinearMap.range D.beta ⧸
          LinearMap.ker (characteristicLambda D)) →ₗ[ℝ]
        (V ⧸ LinearMap.ker (metricClockCovector B u omega)))
    (hpres : ∀ x,
      canonicalClockCovector
          (metricClockCovector B u omega)
          (metricClockCovector_nonzero B u omega homega hu)
          (I x) =
        canonicalClockCovector
          (characteristicLambda D)
          (characteristicLambda_nonzero D)
          x) :
    I =
      (forcedGlobalLocalClockEquiv
        B D u omega homega hu).toLinearMap := by
  exact canonicalClockLineMap_unique
    (characteristicLambda D)
    (characteristicLambda_nonzero D)
    (metricClockCovector B u omega)
    (metricClockCovector_nonzero B u omega homega hu)
    I hpres

end ForcedGlobalLocalClockBridge

end RelativeRest
