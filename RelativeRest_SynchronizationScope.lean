import Mathlib

/-!
# Exactness versus uniqueness of a synchronization correction

The manuscript states that an optical correction beta cancels the anholonomy
  d beta = -d T_O
and vanishes (in the specified principal representative) on a reference
curve.  Those two conditions do not themselves imply uniqueness.

This file gives an explicit, fully finite-dimensional countermodel among
affine one-forms on R^2.  Every affine one-form is represented by its six
coefficients, so exterior differentiation is exactly a constant curl.
An entire one-parameter family beta_c has the SAME curl, vanishes on the SAME
reference line, and renders T_O+beta_c closed, but the beta_c are distinct.

This does not refute uniqueness of beta defined by a fully specified Synge
null-endpoint function. It proves that such an optical existence/uniqueness
theorem is a *necessary upstream premise*, not a consequence of curvature
cancellation and line normalization alone.
-/

namespace RelativeRest
namespace SynchronizationScope

/-- A_t dt + A_x dx, with each coefficient affine in (t,x). -/
structure AffineOneForm where
  at0 : ℝ
  atT : ℝ
  atX : ℝ
  ax0 : ℝ
  axT : ℝ
  axX : ℝ
deriving DecidableEq

/-- The coefficient pair (A_t(t,x), A_x(t,x)). -/
def evaluate (α : AffineOneForm) (t x : ℝ) : ℝ × ℝ :=
  (α.at0 + α.atT * t + α.atX * x,
   α.ax0 + α.axT * t + α.axX * x)

/-- Since α is affine, dα = (∂_t A_x - ∂_x A_t) dt∧dx. -/
def exteriorCurl (α : AffineOneForm) : ℝ :=
  α.axT - α.atX

/-- Non-closed clock covector T_O = -dt + t dx. -/
def localClock : AffineOneForm :=
  ⟨-1, 0, 0, 0, 1, 0⟩

theorem localClock_not_closed :
    exteriorCurl localClock = 1 := by
  norm_num [exteriorCurl, localClock]

/-- beta_c = x dt + c*x dx.
    This entire family obeys d beta_c = -dt∧dx. -/
def correctionFamily (c : ℝ) : AffineOneForm :=
  ⟨0, 0, 1, 0, 0, c⟩

theorem correctionFamily_cancels_curl (c : ℝ) :
    exteriorCurl (correctionFamily c) =
      -exteriorCurl localClock := by
  norm_num [exteriorCurl, correctionFamily, localClock]

/-- Every beta_c vanishes identically along gamma(t)=(t,0). -/
theorem correctionFamily_vanishes_on_reference
    (c t : ℝ) :
    evaluate (correctionFamily c) t 0 = (0, 0) := by
  simp [evaluate, correctionFamily]

/-- Even the full local clock plus beta_c is closed: the cancellation is
    exact for all c, not merely infinitesimal at gamma. -/
def correctedClock (c : ℝ) : AffineOneForm :=
  ⟨-1, 0, 1, 0, 1, c⟩

theorem correctedClock_is_closed (c : ℝ) :
    exteriorCurl (correctedClock c) = 0 := by
  simp [exteriorCurl, correctedClock]

theorem correctedClock_is_local_plus_correction
    (c t x : ℝ) :
    evaluate (correctedClock c) t x =
      (evaluate localClock t x).1 + (evaluate (correctionFamily c) t x).1,
        (evaluate localClock t x).2 + (evaluate (correctionFamily c) t x).2 := by
  simp [evaluate, correctedClock, localClock, correctionFamily]
  ring

/-- The corrections remain distinguishable away from the reference curve. -/
theorem correctionFamily_injective : Function.Injective correctionFamily := by
  intro c d h
  have hX := congrArg AffineOneForm.axX h
  simpa [correctionFamily] using hX

/-- Necessary conditions stated only in terms of exterior derivative and
    reference-curve normalization. -/
def admissibleByCurlAndReference (β : AffineOneForm) : Prop :=
  exteriorCurl β = -exteriorCurl localClock ∧
    ∀ t : ℝ, evaluate β t 0 = (0, 0)

theorem all_corrections_admissible (c : ℝ) :
    admissibleByCurlAndReference (correctionFamily c) := by
  refine ⟨correctionFamily_cancels_curl c, ?_⟩
  exact correctionFamily_vanishes_on_reference c

/-- A genuine counterexample to uniqueness inferred only from curl
    cancellation and vanishing on one reference curve. -/
theorem curl_and_reference_do_not_force_unique_correction :
    ¬ ∃! β : AffineOneForm, admissibleByCurlAndReference β := by
  rintro ⟨β, hβ, hunique⟩
  have h0 : correctionFamily 0 = β :=
    hunique (correctionFamily 0) (all_corrections_admissible 0)
  have h1 : correctionFamily 1 = β :=
    hunique (correctionFamily 1) (all_corrections_admissible 1)
  have h01 : correctionFamily 0 = correctionFamily 1 :=
    h0.trans h1.symm
  have hc := correctionFamily_injective h01
  norm_num at hc

/-- In particular, the family can carry arbitrary exact gradients that
    vanish as one-forms on the reference curve. Hence the optical endpoint
    data must supply more information than these two normalization equations. -/
theorem two_distinct_admissible_corrections :
    ∃ β₀ β₁ : AffineOneForm,
      admissibleByCurlAndReference β₀ ∧
      admissibleByCurlAndReference β₁ ∧
      β₀ ≠ β₁ := by
  refine ⟨correctionFamily 0, correctionFamily 1,
    all_corrections_admissible 0, all_corrections_admissible 1, ?_⟩
  intro h
  have hc := correctionFamily_injective h
  norm_num at hc

end SynchronizationScope
end RelativeRest
