import RelativeRest_DeepPass19

/-!
# Relative Rest: deep forced pass 20

Make the action/optical fixed-point identity explicit.

The common character kappa cancels from the two sector coefficients, so equality of the
Einstein and Maxwell characters is exactly equality of the two optical null weights, exactly
zero rapidity, and exactly s=0.
-/

noncomputable section

open Function Set

namespace RelativeRest

def XiG (kappa s : ℝ) : ℝ :=
  kappa * Real.exp (-s)

def XiM (kappa s : ℝ) : ℝ :=
  kappa * Real.exp s

def nuMinus (s : ℝ) : ℝ :=
  Real.exp (-s)

def nuPlus (s : ℝ) : ℝ :=
  Real.exp s

theorem Xi_rest_iff_zero
    (kappa s : ℝ)
    (hkappa : kappa ≠ 0) :
    XiG kappa s = XiM kappa s ↔ s = 0 := by
  unfold XiG XiM
  constructor
  · intro h
    have hopt : Real.exp (-s) = Real.exp s :=
      mul_left_cancel₀ hkappa h
    exact (action_rest_iff_zero s).mp hopt
  · rintro rfl
    simp

theorem optical_weight_rest_iff_zero
    (s : ℝ) :
    nuMinus s = nuPlus s ↔ s = 0 := by
  exact action_rest_iff_zero s

/-- Equality of the two action characters and equality of the two optical weights are the same
fixed point, with no additional map-dependent condition. -/
theorem action_rest_iff_optical_weight_rest
    (kappa s : ℝ)
    (hkappa : kappa ≠ 0) :
    XiG kappa s = XiM kappa s ↔
      nuMinus s = nuPlus s := by
  rw [Xi_rest_iff_zero kappa s hkappa,
      optical_weight_rest_iff_zero s]

/-- The same fixed point is exactly zero relative optical velocity. -/
theorem action_rest_iff_zero_relative_velocity
    (kappa s : ℝ)
    (hkappa : kappa ≠ 0) :
    XiG kappa s = XiM kappa s ↔
      Real.tanh s = 0 := by
  rw [Xi_rest_iff_zero kappa s hkappa,
      optical_rest_iff_zero s]

/-- Complete fixed-point certificate used by the manuscript's master-ratio discussion. -/
theorem relative_rest_complete_certificate
    (kappa s : ℝ)
    (hkappa : kappa ≠ 0) :
    (XiG kappa s = XiM kappa s ↔ s = 0) ∧
    (nuMinus s = nuPlus s ↔ s = 0) ∧
    (Real.tanh s = 0 ↔ s = 0) := by
  exact
    ⟨Xi_rest_iff_zero kappa s hkappa,
      optical_weight_rest_iff_zero s,
      optical_rest_iff_zero s⟩

end RelativeRest
