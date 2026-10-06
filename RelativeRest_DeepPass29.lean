import RelativeRest_DeepPass28

/-!
# Relative Rest: deep forced pass 29

Construct the intrinsic clock as an actual integral primitive.

For a continuous invariant clock rate omega(tau), define
  Theta(tau) = integral from tau0 to tau of omega(s) ds.
The fundamental theorem of calculus gives Theta'=omega everywhere.  Any differentiable clock with
the same derivative differs from this canonical accumulated clock by one additive constant.

This formalizes the manuscript's integral clock definition and proves its only remaining freedom
is the origin.
-/

noncomputable section

open Function Set
open scoped Interval

namespace RelativeRest

/-- Accumulated intrinsic clock from a chosen additive origin tau0. -/
def accumulatedClock
    (omega : ℝ → ℝ)
    (tau0 tau : ℝ) : ℝ :=
  ∫ s : ℝ in tau0..tau, omega s

@[simp] theorem accumulatedClock_at_origin
    (omega : ℝ → ℝ)
    (tau0 : ℝ) :
    accumulatedClock omega tau0 tau0 = 0 := by
  simp [accumulatedClock]

/-- The accumulated clock is differentiable whenever the invariant rate is continuous. -/
theorem accumulatedClock_differentiable
    (omega : ℝ → ℝ)
    (homega : Continuous omega)
    (tau0 : ℝ) :
    Differentiable ℝ (accumulatedClock omega tau0) := by
  simpa [accumulatedClock] using
    (intervalIntegral.differentiable_integral_of_continuous
      (a := tau0) homega)

/-- Fundamental chronometric equation: dTheta/dtau = omega. -/
theorem accumulatedClock_deriv
    (omega : ℝ → ℝ)
    (homega : Continuous omega)
    (tau0 tau : ℝ) :
    deriv (accumulatedClock omega tau0) tau = omega tau := by
  simpa [accumulatedClock] using
    (Continuous.deriv_integral omega homega tau0 tau)

/-- Any differentiable clock with the same invariant rate differs from the accumulated clock by
one additive constant. -/
theorem clock_with_rate_unique_up_to_origin
    (omega : ℝ → ℝ)
    (homega : Continuous omega)
    (Theta : ℝ → ℝ)
    (hTheta : Differentiable ℝ Theta)
    (hRate : ∀ tau : ℝ, deriv Theta tau = omega tau)
    (tau0 x y : ℝ) :
    Theta x - accumulatedClock omega tau0 x =
      Theta y - accumulatedClock omega tau0 y := by
  apply clock_primitives_differ_by_constant
    Theta
    (accumulatedClock omega tau0)
    hTheta
    (accumulatedClock_differentiable omega homega tau0)
    ?_
    x y
  intro tau
  rw [hRate tau, accumulatedClock_deriv omega homega tau0 tau]

/-- Fixing the value at the chosen origin removes even the additive freedom. -/
theorem clock_with_rate_and_origin_unique
    (omega : ℝ → ℝ)
    (homega : Continuous omega)
    (Theta : ℝ → ℝ)
    (hTheta : Differentiable ℝ Theta)
    (hRate : ∀ tau : ℝ, deriv Theta tau = omega tau)
    (tau0 : ℝ)
    (hOrigin : Theta tau0 = 0)
    (tau : ℝ) :
    Theta tau = accumulatedClock omega tau0 tau := by
  have hconst :=
    clock_with_rate_unique_up_to_origin
      omega homega Theta hTheta hRate tau0 tau tau0
  rw [accumulatedClock_at_origin, hOrigin,
      sub_zero] at hconst
  linarith

end RelativeRest
