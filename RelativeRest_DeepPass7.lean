import RelativeRest_DeepPass6

/-!
# Relative Rest: deep forced pass 7

Kerr--Newman Carter specialization in Boyer--Lindquist components.

This layer removes the remaining algebraic ambiguity in the Carter claim.  It writes the
Boyer--Lindquist metric components explicitly, proves that the standard principal null pair
is null, proves that its zero-boost midpoint is the Carter timelike direction, normalizes that
direction, and derives the displayed angular velocity.

The only upstream geometric input left in this specialization is the standard identification
of these null directions as the repeated principal null directions of Kerr--Newman.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-! ## A. Kerr--Newman Boyer--Lindquist metric algebra -/

def knA (r a : ℝ) : ℝ := r^2 + a^2

def knGtt (r M a Q theta : ℝ) : ℝ :=
  -(Delta r M a Q - a^2 * (Real.sin theta)^2) / Sigma r a theta

def knGtPhi (r M a Q theta : ℝ) : ℝ :=
  -a * (Real.sin theta)^2 *
    (knA r a - Delta r M a Q) / Sigma r a theta

def knGrr (r M a Q theta : ℝ) : ℝ :=
  Sigma r a theta / Delta r M a Q

def knGPhiPhi (r M a Q theta : ℝ) : ℝ :=
  (Real.sin theta)^2 *
    ((knA r a)^2 -
      a^2 * Delta r M a Q * (Real.sin theta)^2) /
      Sigma r a theta

/-- Quadratic form on the t-r-phi subspace at fixed theta. -/
def knTRPhiNorm
    (r M a Q theta t vr vphi : ℝ) : ℝ :=
  knGtt r M a Q theta * t^2 +
  2 * knGtPhi r M a Q theta * t * vphi +
  knGrr r M a Q theta * vr^2 +
  knGPhiPhi r M a Q theta * vphi^2

theorem knA_minus_rotation_eq_Sigma
    (r a theta : ℝ) :
    knA r a - a^2 * (Real.sin theta)^2 =
      Sigma r a theta := by
  have htrig := Real.sin_sq_add_cos_sq theta
  unfold knA Sigma
  nlinarith

/-- The unnormalized Carter timelike direction U=(r^2+a^2,0,a) has norm -Sigma Delta. -/
theorem knCarterDirection_norm
    (r M a Q theta : ℝ)
    (hsig : Sigma r a theta ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    knTRPhiNorm r M a Q theta
      (knA r a) 0 a =
      - Sigma r a theta * Delta r M a Q := by
  have hsine :
      (Real.sin theta)^2 = 1 - (Real.cos theta)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq theta]
  unfold knTRPhiNorm knGtt knGtPhi knGrr knGPhiPhi
  rw [hsine]
  field_simp [hsig, hdel]
  unfold knA Sigma
  ring

/-- The unnormalized radial principal direction E=(0,Delta,0) has norm +Sigma Delta. -/
theorem knRadialDirection_norm
    (r M a Q theta : ℝ)
    (hdel : Delta r M a Q ≠ 0) :
    knTRPhiNorm r M a Q theta
      0 (Delta r M a Q) 0 =
      Sigma r a theta * Delta r M a Q := by
  unfold knTRPhiNorm knGtt knGtPhi knGrr knGPhiPhi
  field_simp [hdel]
  ring

/-- The two standard principal directions U+E and U-E are null. -/
theorem knPrincipalNullPlus_null
    (r M a Q theta : ℝ)
    (hsig : Sigma r a theta ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    knTRPhiNorm r M a Q theta
      (knA r a) (Delta r M a Q) a = 0 := by
  have hU := knCarterDirection_norm r M a Q theta hsig hdel
  have hE := knRadialDirection_norm r M a Q theta hdel
  unfold knTRPhiNorm at hU hE ⊢
  nlinarith

theorem knPrincipalNullMinus_null
    (r M a Q theta : ℝ)
    (hsig : Sigma r a theta ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    knTRPhiNorm r M a Q theta
      (knA r a) (-Delta r M a Q) a = 0 := by
  have hU := knCarterDirection_norm r M a Q theta hsig hdel
  have hE := knRadialDirection_norm r M a Q theta hdel
  unfold knTRPhiNorm at hU hE ⊢
  nlinarith

/-! ## B. Zero boost is exactly the Carter midpoint -/

def knBalancedT
    (r a sigma : ℝ) : ℝ :=
  (Real.exp (-sigma) * knA r a +
    Real.exp sigma * knA r a) / 2

def knBalancedR
    (r M a Q sigma : ℝ) : ℝ :=
  (Real.exp (-sigma) * Delta r M a Q +
    Real.exp sigma * (-Delta r M a Q)) / 2

def knBalancedPhi
    (a sigma : ℝ) : ℝ :=
  (Real.exp (-sigma) * a + Real.exp sigma * a) / 2

@[simp] theorem knBalancedT_zero (r a : ℝ) :
    knBalancedT r a 0 = knA r a := by
  simp [knBalancedT]

@[simp] theorem knBalancedR_zero (r M a Q : ℝ) :
    knBalancedR r M a Q 0 = 0 := by
  simp [knBalancedR]

@[simp] theorem knBalancedPhi_zero (a : ℝ) :
    knBalancedPhi a 0 = a := by
  simp [knBalancedPhi]

/-- A resolved purely radial carrier balance forces the balanced principal midpoint to be the
standard Carter direction, with no radial component. -/
theorem kn_balance_forces_Carter_midpoint
    (r M a Q q sigma : ℝ)
    (hq : q ≠ 0)
    (hbal : boostDefect (-q) q sigma = 0) :
    knBalancedT r a sigma = knA r a ∧
    knBalancedR r M a Q sigma = 0 ∧
    knBalancedPhi a sigma = a := by
  have hsigma : sigma = 0 :=
    (pure_radial_boost_balance_iff_zero q sigma hq).mp hbal
  subst sigma
  simp

/-! ## C. Carter normalization and angular velocity -/

def knCarterNormFactor
    (r M a Q theta : ℝ) : ℝ :=
  Real.sqrt (Sigma r a theta * Delta r M a Q)

theorem knCarterNormFactor_sq
    (r M a Q theta : ℝ)
    (hpos : 0 ≤ Sigma r a theta * Delta r M a Q) :
    (knCarterNormFactor r M a Q theta)^2 =
      Sigma r a theta * Delta r M a Q := by
  unfold knCarterNormFactor
  exact Real.sq_sqrt hpos

theorem knTRPhiNorm_stationary_scale
    (r M a Q theta c t vphi : ℝ) :
    knTRPhiNorm r M a Q theta
      (c * t) 0 (c * vphi) =
      c^2 * knTRPhiNorm r M a Q theta t 0 vphi := by
  unfold knTRPhiNorm
  ring

/-- On the exterior/timelike region Sigma Delta>0, the normalized Carter direction is unit
timelike. -/
theorem knCarterDirection_unit_norm
    (r M a Q theta : ℝ)
    (hprod : 0 < Sigma r a theta * Delta r M a Q) :
    knTRPhiNorm r M a Q theta
      (knA r a / knCarterNormFactor r M a Q theta)
      0
      (a / knCarterNormFactor r M a Q theta) = -1 := by
  have hsig : Sigma r a theta ≠ 0 := by
    intro hs
    rw [hs, zero_mul] at hprod
    exact (lt_irrefl 0) hprod
  have hdel : Delta r M a Q ≠ 0 := by
    intro hd
    rw [hd, mul_zero] at hprod
    exact (lt_irrefl 0) hprod
  have hNpos : 0 < knCarterNormFactor r M a Q theta := by
    unfold knCarterNormFactor
    exact Real.sqrt_pos.2 hprod
  have hN0 : knCarterNormFactor r M a Q theta ≠ 0 := ne_of_gt hNpos
  have hN2 :
      (knCarterNormFactor r M a Q theta)^2 =
        Sigma r a theta * Delta r M a Q :=
    knCarterNormFactor_sq r M a Q theta (le_of_lt hprod)
  have hU := knCarterDirection_norm r M a Q theta hsig hdel
  rw [show knA r a / knCarterNormFactor r M a Q theta =
        (knCarterNormFactor r M a Q theta)⁻¹ * knA r a by
          field_simp [hN0],
      show a / knCarterNormFactor r M a Q theta =
        (knCarterNormFactor r M a Q theta)⁻¹ * a by
          field_simp [hN0],
      knTRPhiNorm_stationary_scale]
  rw [hU]
  field_simp [hN0]
  nlinarith [hN2]

/-- The ratio of the normalized phi and t components is the Carter angular velocity. -/
theorem knCarter_angular_velocity
    (r M a Q theta : ℝ)
    (hprod : 0 < Sigma r a theta * Delta r M a Q)
    (hA : knA r a ≠ 0) :
    (a / knCarterNormFactor r M a Q theta) /
      (knA r a / knCarterNormFactor r M a Q theta) =
      a / knA r a := by
  have hN0 : knCarterNormFactor r M a Q theta ≠ 0 := by
    unfold knCarterNormFactor
    exact ne_of_gt (Real.sqrt_pos.2 hprod)
  field_simp [hN0, hA]

/-- Combining the radial fixed-point carrier with the Boyer--Lindquist metric: the unique balanced
principal midpoint is the normalized Carter observer.  The first three equalities identify its
coordinate direction, and the last establishes its unit timelike normalization. -/
theorem kn_Carter_observer_certificate
    (r M a Q theta q sigma : ℝ)
    (hq : q ≠ 0)
    (hbal : boostDefect (-q) q sigma = 0)
    (hprod : 0 < Sigma r a theta * Delta r M a Q) :
    knBalancedT r a sigma = knA r a ∧
    knBalancedR r M a Q sigma = 0 ∧
    knBalancedPhi a sigma = a ∧
    knTRPhiNorm r M a Q theta
      (knA r a / knCarterNormFactor r M a Q theta)
      0
      (a / knCarterNormFactor r M a Q theta) = -1 := by
  rcases kn_balance_forces_Carter_midpoint
      r M a Q q sigma hq hbal with ⟨ht, hr, hp⟩
  exact ⟨ht, hr, hp,
    knCarterDirection_unit_norm r M a Q theta hprod⟩

end RelativeRest
