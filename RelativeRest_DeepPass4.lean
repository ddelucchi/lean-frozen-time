import RelativeRest_DeepPass3

/-!
# Relative Rest: deep forced pass 4

This layer formalizes the local pointwise clock response and the unique normalized
local/global clock identification.  It deliberately keeps only the actual geometric current
as an upstream interface; coefficient uniqueness, normalization, quotient dimension, and the
clock-line isomorphism are derived.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-! ## A. Positive values force nonzero covectors -/

section PositiveCovector

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem covector_nonzero_of_positive_value
    (ell : V →ₗ[ℝ] ℝ) (v : V)
    (hpos : 0 < ell v) :
    ell ≠ 0 := by
  intro hzero
  rw [hzero] at hpos
  simp at hpos

end PositiveCovector

/-! ## B. Pointwise rank-one Iyer--Wald clock response -/

section PointwiseClockResponse

variable {V W : Type*}
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [NoZeroSMulDivisors ℝ W]

structure PointwiseClockResponseData where
  response : V → W
  carrier : W
  carrier_nonzero : carrier ≠ 0
  lambda : V →ₗ[ℝ] ℝ
  uhat : V
  factorization : ∀ v : V, response v = (lambda v) • carrier
  unit_response : response uhat = carrier

/-- The pointwise current itself forces the local clock normalization lambda(uhat)=1. -/
theorem pointwise_clock_normalized
    (D : PointwiseClockResponseData (V:=V) (W:=W)) :
    D.lambda D.uhat = 1 := by
  exact covector_normalized_from_unit_response
    D.carrier D.carrier_nonzero D.response D.lambda D.uhat
    D.factorization D.unit_response

/-- The normalized local clock covector is nonzero without an extra assumption. -/
theorem pointwise_clock_lambda_nonzero
    (D : PointwiseClockResponseData (V:=V) (W:=W)) :
    D.lambda ≠ 0 := by
  intro hzero
  have hnorm := pointwise_clock_normalized D
  rw [hzero] at hnorm
  simp at hnorm

/-- No second local covector can factor the same nonzero rank-one current. -/
theorem pointwise_clock_lambda_unique
    (D : PointwiseClockResponseData (V:=V) (W:=W))
    (alpha : V →ₗ[ℝ] ℝ)
    (halpha : ∀ v : V, D.response v = (alpha v) • D.carrier) :
    alpha = D.lambda := by
  exact rank_one_response_factorization_unique
    D.carrier D.carrier_nonzero D.response alpha D.lambda
    halpha D.factorization

/-- The local stress-visible quotient is canonically a real line. -/
noncomputable def pointwiseClockLine
    (D : PointwiseClockResponseData (V:=V) (W:=W)) :
    (V ⧸ LinearMap.ker D.lambda) ≃ₗ[ℝ] ℝ :=
  clockQuotientEquivReal D.lambda (pointwise_clock_lambda_nonzero D)

/-- Every vector is its clock component plus a vector invisible to the pointwise current. -/
theorem pointwise_clock_decomposition
    (D : PointwiseClockResponseData (V:=V) (W:=W))
    (v : V) :
    D.lambda (v - (D.lambda v) • D.uhat) = 0 := by
  simp [pointwise_clock_normalized D]

end PointwiseClockResponse

/-! ## C. Unique normalized isomorphism between one-dimensional clock lines -/

section ClockLineIso

variable {L1 L2 : Type*}
  [AddCommGroup L1] [Module ℝ L1]
  [AddCommGroup L2] [Module ℝ L2]

/-- Once both clock lines carry fixed normalized covectors, the covector-preserving map is a
linear equivalence and has no remaining multiplicative freedom. -/
def normalizedClockEquiv
    (alpha : L1 →ₗ[ℝ] ℝ)
    (beta : L2 →ₗ[ℝ] ℝ)
    (u1 : L1) (u2 : L2)
    (halpha : alpha u1 = 1)
    (hbeta : beta u2 = 1)
    (hspan1 : ∀ x : L1, x = (alpha x) • u1)
    (hspan2 : ∀ y : L2, y = (beta y) • u2) :
    L1 ≃ₗ[ℝ] L2 := by
  refine LinearEquiv.ofLinearMap
    (normalizedClockMap alpha u2)
    (normalizedClockMap beta u1) ?_ ?_
  · apply LinearMap.ext
    intro y
    exact normalizedClockMap_roundtrip_right
      alpha beta u1 u2 halpha hspan2 y
  · apply LinearMap.ext
    intro x
    exact normalizedClockMap_roundtrip_left
      alpha beta u1 u2 hbeta hspan1 x

theorem normalizedClockEquiv_preserves_covector
    (alpha : L1 →ₗ[ℝ] ℝ)
    (beta : L2 →ₗ[ℝ] ℝ)
    (u1 : L1) (u2 : L2)
    (halpha : alpha u1 = 1)
    (hbeta : beta u2 = 1)
    (hspan1 : ∀ x : L1, x = (alpha x) • u1)
    (hspan2 : ∀ y : L2, y = (beta y) • u2)
    (x : L1) :
    beta (normalizedClockEquiv alpha beta u1 u2
      halpha hbeta hspan1 hspan2 x) = alpha x := by
  change beta (normalizedClockMap alpha u2 x) = alpha x
  exact normalizedClockMap_preserves_covector alpha beta u2 hbeta x

theorem normalizedClockEquiv_maps_unit
    (alpha : L1 →ₗ[ℝ] ℝ)
    (beta : L2 →ₗ[ℝ] ℝ)
    (u1 : L1) (u2 : L2)
    (halpha : alpha u1 = 1)
    (hbeta : beta u2 = 1)
    (hspan1 : ∀ x : L1, x = (alpha x) • u1)
    (hspan2 : ∀ y : L2, y = (beta y) • u2) :
    normalizedClockEquiv alpha beta u1 u2
      halpha hbeta hspan1 hspan2 u1 = u2 := by
  change normalizedClockMap alpha u2 u1 = u2
  simp [normalizedClockMap, halpha]

/-- Any linear map carrying the normalized unit to the normalized unit agrees with the forced
clock-line isomorphism. -/
theorem normalizedClockEquiv_unique
    (alpha : L1 →ₗ[ℝ] ℝ)
    (beta : L2 →ₗ[ℝ] ℝ)
    (u1 : L1) (u2 : L2)
    (halpha : alpha u1 = 1)
    (hbeta : beta u2 = 1)
    (hspan1 : ∀ x : L1, x = (alpha x) • u1)
    (hspan2 : ∀ y : L2, y = (beta y) • u2)
    (I : L1 →ₗ[ℝ] L2)
    (hIu : I u1 = u2) :
    I = (normalizedClockEquiv alpha beta u1 u2
      halpha hbeta hspan1 hspan2).toLinearMap := by
  exact unique_covector_preserving_map
    alpha beta u1 u2 halpha hbeta hspan1 hspan2
    I
    (normalizedClockEquiv alpha beta u1 u2
      halpha hbeta hspan1 hspan2).toLinearMap
    hIu
    (normalizedClockEquiv_maps_unit
      alpha beta u1 u2 halpha hbeta hspan1 hspan2)

end ClockLineIso

/-! ## D. Global and local normalized units are forced to correspond -/

section UnitCorrespondence

variable {L1 L2 : Type*}
  [AddCommGroup L1] [Module ℝ L1]
  [AddCommGroup L2] [Module ℝ L2]

theorem normalized_unit_unique
    (alpha : L1 →ₗ[ℝ] ℝ)
    (u v : L1)
    (hspan : ∀ x : L1, x = (alpha x) • u)
    (hu : alpha u = 1)
    (hv : alpha v = 1) :
    v = u := by
  calc
    v = (alpha v) • u := hspan v
    _ = u := by simp [hv]

end UnitCorrespondence

end RelativeRest
