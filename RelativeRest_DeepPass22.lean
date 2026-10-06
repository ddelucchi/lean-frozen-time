import RelativeRest_DeepPass21

/-!
# Relative Rest: deep forced pass 22

Formalize the operational optical defect.

On the balanced generating orbit the radial response vanishes, while its first boost derivative is
the nonzero carrier coefficient.  Away from rest, the ratio of radial to timelike optical response
is exactly tanh(s), and therefore equals the action-side even/odd carrier ratio.
-/

noncomputable section

open Function Set

namespace RelativeRest

def opticalTimeResponse (s : ℝ) : ℝ :=
  Real.cosh s

def opticalRadialResponse (s : ℝ) : ℝ :=
  Real.sinh s

@[simp] theorem opticalRadialResponse_zero :
    opticalRadialResponse 0 = 0 := by
  simp [opticalRadialResponse]

@[simp] theorem opticalTimeResponse_zero :
    opticalTimeResponse 0 = 1 := by
  simp [opticalTimeResponse]

/-- The optical radial defect has unit first rapidity jet at relative rest. -/
theorem opticalRadialResponse_hasDerivAt_zero :
    HasDerivAt opticalRadialResponse 1 0 := by
  simpa [opticalRadialResponse] using Real.hasDerivAt_sinh 0

/-- With a nonzero carrier coefficient q, the radial observable vanishes at rest but its first
normal derivative is q and therefore survives. -/
theorem pureRadialObserverResponse_fixed_point_jet
    (q : ℝ)
    (hq : q ≠ 0) :
    pureRadialObserverResponse q 0 = 0 ∧
    HasDerivAt (pureRadialObserverResponse q) q 0 ∧
    q ≠ 0 := by
  constructor
  · simp [pureRadialObserverResponse]
  · constructor
    · unfold pureRadialObserverResponse
      simpa using (Real.hasDerivAt_sinh 0).const_mul q
    · exact hq

/-- The operational radial/time optical velocity is exactly the rapidity velocity tanh(s). -/
theorem optical_response_ratio_eq_tanh
    (s : ℝ) :
    opticalRadialResponse s / opticalTimeResponse s =
      Real.tanh s := by
  rw [Real.tanh_eq_sinh_div_cosh]
  rfl

/-- The action-side odd/even carrier ratio and the optical radial/time response ratio coincide. -/
theorem carrier_ratio_eq_optical_velocity
    (eta s : ℝ)
    (heta : eta ≠ 0) :
    - carrierOdd eta s / carrierEven eta s =
      opticalRadialResponse s / opticalTimeResponse s := by
  rw [carrier_ratio eta s heta, optical_response_ratio_eq_tanh]

/-- Complete defect-velocity identity used in the manuscript. -/
theorem defect_velocity_certificate
    (eta s : ℝ)
    (heta : eta ≠ 0) :
    - carrierOdd eta s / carrierEven eta s =
      opticalRadialResponse s / opticalTimeResponse s ∧
    opticalRadialResponse s / opticalTimeResponse s =
      Real.tanh s := by
  exact
    ⟨carrier_ratio_eq_optical_velocity eta s heta,
      optical_response_ratio_eq_tanh s⟩

end RelativeRest
