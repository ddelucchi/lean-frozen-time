import RelativeRest_DeepPass23

/-!
# Relative Rest: deep forced pass 24

Formalize the normal/clock-dual identification.

For any canonical clock quotient L=K/ker(Lambda), every element of L is reconstructed from its
clock coordinate and canonical unit.  Dually, every covector on L is reconstructed from its value
on that unit.  Applying this to the characteristic clock line gives an explicit linear equivalence
between the relative action-normal quotient and the dual characteristic clock line.

This is the algebraic content of N_Phi ~= L_Phi^* with no basis choice.
-/

noncomputable section

open Function Set

namespace RelativeRest

section CanonicalClockDual

variable {K : Type*} [AddCommGroup K] [Module ℝ K]

/-- Every covector on a canonical one-dimensional clock quotient is a scalar multiple of the
forced clock covector, with coefficient equal to its value on the canonical unit. -/
theorem canonicalClockDual_reconstruction
    (Lambda : K →ₗ[ℝ] ℝ)
    (hLambda : Lambda ≠ 0)
    (alpha : Module.Dual ℝ (K ⧸ LinearMap.ker Lambda)) :
    alpha =
      (alpha (canonicalClockUnit Lambda hLambda)) •
        canonicalClockCovector Lambda hLambda := by
  ext x
  rw [canonicalClock_reconstruction Lambda hLambda x]
  simp [canonicalClockCovector_unit]
  ring

end CanonicalClockDual

section RelativeNormalClockDual

variable {P K : Type*}
  [AddCommGroup P] [Module ℝ P]
  [AddCommGroup K] [Module ℝ K]

/-- The relative action normal acts on the characteristic clock line by its canonical scalar
coordinate multiplying the forced clock covector. -/
noncomputable def relativeNormalToClockDual
    (D : CharacteristicResponseData (P:=P) (K:=K)) :
    (R2 ⧸ LinearMap.ker relativeScaleCovector) →ₗ[ℝ]
      Module.Dual ℝ
        (LinearMap.range D.beta ⧸
          LinearMap.ker (characteristicLambda D)) where
  toFun n :=
    (canonicalClockCovector
      relativeScaleCovector
      relativeScaleCovector_nonzero n) •
      canonicalClockCovector
        (characteristicLambda D)
        (characteristicLambda_nonzero D)
  map_add' x y := by
    simp [add_smul]
  map_smul' c x := by
    simp [mul_smul]

/-- Evaluation on the characteristic clock unit reconstructs the corresponding relative normal. -/
noncomputable def clockDualToRelativeNormal
    (D : CharacteristicResponseData (P:=P) (K:=K)) :
    Module.Dual ℝ
        (LinearMap.range D.beta ⧸
          LinearMap.ker (characteristicLambda D)) →ₗ[ℝ]
      (R2 ⧸ LinearMap.ker relativeScaleCovector) where
  toFun alpha :=
    (alpha
      (canonicalClockUnit
        (characteristicLambda D)
        (characteristicLambda_nonzero D))) •
      canonicalClockUnit
        relativeScaleCovector
        relativeScaleCovector_nonzero
  map_add' alpha beta := by
    simp [add_smul]
  map_smul' c alpha := by
    simp [mul_smul]

theorem clockDualToRelativeNormal_after_relativeNormalToClockDual
    (D : CharacteristicResponseData (P:=P) (K:=K))
    (n : R2 ⧸ LinearMap.ker relativeScaleCovector) :
    clockDualToRelativeNormal D
        (relativeNormalToClockDual D n) = n := by
  unfold clockDualToRelativeNormal relativeNormalToClockDual
  simp [canonicalClockCovector_unit]
  exact
    (canonicalClock_reconstruction
      relativeScaleCovector
      relativeScaleCovector_nonzero n).symm

theorem relativeNormalToClockDual_after_clockDualToRelativeNormal
    (D : CharacteristicResponseData (P:=P) (K:=K))
    (alpha :
      Module.Dual ℝ
        (LinearMap.range D.beta ⧸
          LinearMap.ker (characteristicLambda D))) :
    relativeNormalToClockDual D
        (clockDualToRelativeNormal D alpha) = alpha := by
  unfold clockDualToRelativeNormal relativeNormalToClockDual
  simp [canonicalClockCovector_unit]
  exact
    (canonicalClockDual_reconstruction
      (characteristicLambda D)
      (characteristicLambda_nonzero D)
      alpha).symm

/-- The relative scale-normal line is canonically the dual characteristic clock line. -/
noncomputable def relativeNormalClockDualEquiv
    (D : CharacteristicResponseData (P:=P) (K:=K)) :
    (R2 ⧸ LinearMap.ker relativeScaleCovector) ≃ₗ[ℝ]
      Module.Dual ℝ
        (LinearMap.range D.beta ⧸
          LinearMap.ker (characteristicLambda D)) := by
  refine LinearEquiv.ofLinearMap
    (relativeNormalToClockDual D)
    (clockDualToRelativeNormal D) ?_ ?_
  · apply LinearMap.ext
    intro alpha
    exact
      relativeNormalToClockDual_after_clockDualToRelativeNormal D alpha
  · apply LinearMap.ext
    intro n
    exact
      clockDualToRelativeNormal_after_relativeNormalToClockDual D n

end RelativeNormalClockDual

end RelativeRest
