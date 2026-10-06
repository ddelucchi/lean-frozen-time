import RelativeRest_DeepPass14

/-!
# Relative Rest: deep forced pass 15

Make the characteristic clock line completely canonical.

A nonzero characteristic covector Lambda already forces the quotient K/ker Lambda to be a real
line.  This file removes the remaining "choose a normalized unit / assume a spanning relation"
interfaces: the quotient equivalence itself constructs the clock covector, the unit clock
direction, reconstruction of every quotient vector, and the unique covector-preserving
identification between any two such clock lines.
-/

noncomputable section

open Function Set

namespace RelativeRest

section CanonicalClockQuotient

variable {K : Type*} [AddCommGroup K] [Module ℝ K]

/-- The descended clock covector is the canonical quotient-to-real equivalence. -/
noncomputable def canonicalClockCovector
    (Lambda : K →ₗ[ℝ] ℝ)
    (hLambda : Lambda ≠ 0) :
    (K ⧸ LinearMap.ker Lambda) →ₗ[ℝ] ℝ :=
  (clockQuotientEquivReal Lambda hLambda).toLinearMap

/-- The positive normalized clock element is the inverse image of 1. -/
noncomputable def canonicalClockUnit
    (Lambda : K →ₗ[ℝ] ℝ)
    (hLambda : Lambda ≠ 0) :
    K ⧸ LinearMap.ker Lambda :=
  (clockQuotientEquivReal Lambda hLambda).symm 1

@[simp] theorem canonicalClockCovector_unit
    (Lambda : K →ₗ[ℝ] ℝ)
    (hLambda : Lambda ≠ 0) :
    canonicalClockCovector Lambda hLambda
      (canonicalClockUnit Lambda hLambda) = 1 := by
  simp [canonicalClockCovector, canonicalClockUnit]

/-- No spanning hypothesis is needed: every quotient vector is reconstructed from its unique
clock coordinate and the canonical unit. -/
theorem canonicalClock_reconstruction
    (Lambda : K →ₗ[ℝ] ℝ)
    (hLambda : Lambda ≠ 0)
    (x : K ⧸ LinearMap.ker Lambda) :
    x =
      (canonicalClockCovector Lambda hLambda x) •
        canonicalClockUnit Lambda hLambda := by
  let E := clockQuotientEquivReal Lambda hLambda
  apply E.injective
  simp [E, canonicalClockCovector, canonicalClockUnit]

/-- The normalized quotient generator is forced; there is no residual multiplicative freedom. -/
theorem canonicalClockUnit_unique
    (Lambda : K →ₗ[ℝ] ℝ)
    (hLambda : Lambda ≠ 0)
    (u : K ⧸ LinearMap.ker Lambda)
    (hu : canonicalClockCovector Lambda hLambda u = 1) :
    u = canonicalClockUnit Lambda hLambda := by
  calc
    u =
        (canonicalClockCovector Lambda hLambda u) •
          canonicalClockUnit Lambda hLambda :=
      canonicalClock_reconstruction Lambda hLambda u
    _ = canonicalClockUnit Lambda hLambda := by
      rw [hu]
      simp

end CanonicalClockQuotient

section CanonicalClockIdentification

variable {K1 K2 : Type*}
  [AddCommGroup K1] [Module ℝ K1]
  [AddCommGroup K2] [Module ℝ K2]

/-- The unique normalized identification of two characteristic clock quotients is composition
through their forced real clock coordinate. -/
noncomputable def canonicalClockLineEquiv
    (Lambda1 : K1 →ₗ[ℝ] ℝ) (h1 : Lambda1 ≠ 0)
    (Lambda2 : K2 →ₗ[ℝ] ℝ) (h2 : Lambda2 ≠ 0) :
    (K1 ⧸ LinearMap.ker Lambda1) ≃ₗ[ℝ]
      (K2 ⧸ LinearMap.ker Lambda2) :=
  (clockQuotientEquivReal Lambda1 h1) ≪≫ₗ
    (clockQuotientEquivReal Lambda2 h2).symm

theorem canonicalClockLineEquiv_preserves_covector
    (Lambda1 : K1 →ₗ[ℝ] ℝ) (h1 : Lambda1 ≠ 0)
    (Lambda2 : K2 →ₗ[ℝ] ℝ) (h2 : Lambda2 ≠ 0)
    (x : K1 ⧸ LinearMap.ker Lambda1) :
    canonicalClockCovector Lambda2 h2
        (canonicalClockLineEquiv Lambda1 h1 Lambda2 h2 x) =
      canonicalClockCovector Lambda1 h1 x := by
  simp [canonicalClockCovector, canonicalClockLineEquiv]

@[simp] theorem canonicalClockLineEquiv_maps_unit
    (Lambda1 : K1 →ₗ[ℝ] ℝ) (h1 : Lambda1 ≠ 0)
    (Lambda2 : K2 →ₗ[ℝ] ℝ) (h2 : Lambda2 ≠ 0) :
    canonicalClockLineEquiv Lambda1 h1 Lambda2 h2
        (canonicalClockUnit Lambda1 h1) =
      canonicalClockUnit Lambda2 h2 := by
  simp [canonicalClockLineEquiv, canonicalClockUnit]

/-- Covector preservation alone forces the map between the already-canonical clock quotients. -/
theorem canonicalClockLineMap_unique
    (Lambda1 : K1 →ₗ[ℝ] ℝ) (h1 : Lambda1 ≠ 0)
    (Lambda2 : K2 →ₗ[ℝ] ℝ) (h2 : Lambda2 ≠ 0)
    (I : (K1 ⧸ LinearMap.ker Lambda1) →ₗ[ℝ]
      (K2 ⧸ LinearMap.ker Lambda2))
    (hpres : ∀ x,
      canonicalClockCovector Lambda2 h2 (I x) =
        canonicalClockCovector Lambda1 h1 x) :
    I = (canonicalClockLineEquiv Lambda1 h1 Lambda2 h2).toLinearMap := by
  ext x
  apply (clockQuotientEquivReal Lambda2 h2).injective
  exact hpres x

end CanonicalClockIdentification

end RelativeRest
