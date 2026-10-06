import RelativeRest_DeepPass9

/-!
# Relative Rest: deep forced pass 10

Complete the algebraic Kerr--Newman carrier-to-Carter chain.

The previous files derived d_r log chi = -4 r / Sigma and proved that opposite radial null
responses force zero boost.  Here the actual Kerr--Newman radial carrier coefficient is inserted
into the principal null pair, its nonvanishing conditions are derived, and the unique balance is
shown to be sigma=0 without an arbitrary response parameter.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-! ## A. Specialize the radial carrier to Kerr--Newman Sigma -/

theorem knSigmaRadial_specializes
    (r a theta : ℝ) :
    knSigmaRadial (a^2 * (Real.cos theta)^2) r =
      Sigma r a theta := by
  rfl

def knRadialCarrierCoeff
    (r a theta : ℝ) : ℝ :=
  -4 * r / Sigma r a theta

/-- The exact radial logarithmic carrier derivative appearing in the manuscript. -/
theorem knLogChi_hasRadialDerivative
    (Q r a theta : ℝ)
    (hQ : Q ≠ 0)
    (hsig : Sigma r a theta ≠ 0) :
    HasDerivAt
      (fun x =>
        Real.log
          (knChiRadial Q
            (a^2 * (Real.cos theta)^2) x))
      (knRadialCarrierCoeff r a theta) r := by
  have h :=
    knLogChiRadial_hasDerivAt
      Q (a^2 * (Real.cos theta)^2) r hQ
      (by simpa [knSigmaRadial_specializes] using hsig)
  simpa [knRadialCarrierCoeff, knSigmaRadial_specializes] using h

/-! ## B. Principal-null responses of the radial carrier -/

def knRadialResponsePlus
    (r M a Q theta : ℝ) : ℝ :=
  knRadialCarrierCoeff r a theta * Delta r M a Q

def knRadialResponseMinus
    (r M a Q theta : ℝ) : ℝ :=
  - knRadialCarrierCoeff r a theta * Delta r M a Q

theorem knRadialResponses_opposite
    (r M a Q theta : ℝ) :
    knRadialResponseMinus r M a Q theta =
      - knRadialResponsePlus r M a Q theta := by
  unfold knRadialResponseMinus knRadialResponsePlus
  ring

theorem knRadialCarrierCoeff_ne_zero
    (r a theta : ℝ)
    (hr : r ≠ 0)
    (hsig : Sigma r a theta ≠ 0) :
    knRadialCarrierCoeff r a theta ≠ 0 := by
  unfold knRadialCarrierCoeff
  exact div_ne_zero
    (mul_ne_zero (by norm_num) hr)
    hsig

theorem knRadialResponsePlus_ne_zero
    (r M a Q theta : ℝ)
    (hr : r ≠ 0)
    (hsig : Sigma r a theta ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    knRadialResponsePlus r M a Q theta ≠ 0 := by
  unfold knRadialResponsePlus
  exact mul_ne_zero
    (knRadialCarrierCoeff_ne_zero r a theta hr hsig)
    hdel

/-! ## C. The actual carrier balance forces sigma=0 -/

/-- For the Kerr--Newman radial carrier, the boost defect is the pure opposite-response defect. -/
theorem knCarrierBoostDefect_eq
    (r M a Q theta sigma : ℝ) :
    boostDefect
      (knRadialResponseMinus r M a Q theta)
      (knRadialResponsePlus r M a Q theta)
      sigma =
    boostDefect
      (-knRadialResponsePlus r M a Q theta)
      (knRadialResponsePlus r M a Q theta)
      sigma := by
  rw [knRadialResponses_opposite]

/-- Away from the unresolved r=0/Delta=0 strata, the carrier balance has the unique root sigma=0. -/
theorem knCarrier_balance_iff_zero
    (r M a Q theta sigma : ℝ)
    (hr : r ≠ 0)
    (hsig : Sigma r a theta ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    boostDefect
      (knRadialResponseMinus r M a Q theta)
      (knRadialResponsePlus r M a Q theta)
      sigma = 0 ↔ sigma = 0 := by
  rw [knCarrierBoostDefect_eq]
  exact pure_radial_boost_balance_iff_zero
    (knRadialResponsePlus r M a Q theta)
    sigma
    (knRadialResponsePlus_ne_zero
      r M a Q theta hr hsig hdel)

/-- The displayed sigmaStar formula itself collapses to zero for the Kerr--Newman radial carrier. -/
theorem knCarrier_sigmaStar_eq_zero
    (r M a Q theta : ℝ)
    (hr : r ≠ 0)
    (hsig : Sigma r a theta ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    sigmaStar
      (knRadialResponseMinus r M a Q theta)
      (knRadialResponsePlus r M a Q theta) = 0 := by
  let q := knRadialResponsePlus r M a Q theta
  have hq : q ≠ 0 :=
    knRadialResponsePlus_ne_zero
      r M a Q theta hr hsig hdel
  have hminus :
      knRadialResponseMinus r M a Q theta = -q := by
    dsimp [q]
    exact knRadialResponses_opposite r M a Q theta
  rw [hminus]
  unfold sigmaStar
  have hratio : (-q) / q = -1 := by
    field_simp [hq]
  rw [hratio]
  norm_num

/-- Therefore the actual field-derived Kerr--Newman carrier balance selects the Carter midpoint. -/
theorem knFieldCarrier_forces_Carter_midpoint
    (r M a Q theta sigma : ℝ)
    (hr : r ≠ 0)
    (hsig : Sigma r a theta ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hbal :
      boostDefect
        (knRadialResponseMinus r M a Q theta)
        (knRadialResponsePlus r M a Q theta)
        sigma = 0) :
    knBalancedT r a sigma = knA r a ∧
    knBalancedR r M a Q sigma = 0 ∧
    knBalancedPhi a sigma = a := by
  have hsigma :
      sigma = 0 :=
    (knCarrier_balance_iff_zero
      r M a Q theta sigma hr hsig hdel).mp hbal
  subst sigma
  simp

/-- Full field-carrier-to-unit-Carter-observer certificate on the regular exterior branch. -/
theorem knFieldCarrier_Carter_observer_certificate
    (r M a Q theta sigma : ℝ)
    (hr : r ≠ 0)
    (hbal :
      boostDefect
        (knRadialResponseMinus r M a Q theta)
        (knRadialResponsePlus r M a Q theta)
        sigma = 0)
    (hprod : 0 < Sigma r a theta * Delta r M a Q) :
    knBalancedT r a sigma = knA r a ∧
    knBalancedR r M a Q sigma = 0 ∧
    knBalancedPhi a sigma = a ∧
    knTRPhiNorm r M a Q theta
      (knA r a / knCarterNormFactor r M a Q theta)
      0
      (a / knCarterNormFactor r M a Q theta) = -1 := by
  have hsig : Sigma r a theta ≠ 0 := by
    intro hs
    rw [hs, zero_mul] at hprod
    linarith
  have hdel : Delta r M a Q ≠ 0 := by
    intro hd
    rw [hd, mul_zero] at hprod
    linarith
  rcases knFieldCarrier_forces_Carter_midpoint
      r M a Q theta sigma hr hsig hdel hbal with
    ⟨ht, hrad, hphi⟩
  exact ⟨ht, hrad, hphi,
    knCarterDirection_unit_norm r M a Q theta hprod⟩

end RelativeRest
