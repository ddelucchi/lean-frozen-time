import RelativeRest_DeepPass25

/-!
# Relative Rest: deep forced pass 26

Remove the remaining abstract factorization from the pointwise Iyer--Wald clock normalization.

Once the manuscript-specific local response has the explicit form
  w(v)|_H = (omega/(8*pi)) T_O(v) epsilon_H,
its nonzero carrier, normalized unit response, and unique scalar coefficient are consequences.
Specializing T_O to the metric-derived covector -omega g(u,.) therefore forces lambda_x=T_O
without supplying lambda_x or its factorization as independent data.
-/

noncomputable section

open Function Set

namespace RelativeRest

section ExplicitLocalIW

variable {V W : Type*}
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [NoZeroSMulDivisors ℝ W]

/-- The nonzero principal-rest carrier three-form, abstracted only by its target module element. -/
def localIWCarrier
    (epsilonH : W) (omega : ℝ) : W :=
  (omega / (8 * Real.pi)) • epsilonH

/-- The paper-specific restricted pointwise response. -/
def localIWResponse
    (T : V →ₗ[ℝ] ℝ)
    (epsilonH : W)
    (omega : ℝ) :
    V →ₗ[ℝ] W where
  toFun v := (T v) • localIWCarrier epsilonH omega
  map_add' x y := by
    simp [add_smul]
  map_smul' c x := by
    simp [mul_smul]

@[simp] theorem localIWResponse_apply
    (T : V →ₗ[ℝ] ℝ)
    (epsilonH : W)
    (omega : ℝ)
    (v : V) :
    localIWResponse T epsilonH omega v =
      (T v) • localIWCarrier epsilonH omega := rfl

theorem localIWCarrier_nonzero
    (epsilonH : W)
    (omega : ℝ)
    (homega : omega ≠ 0)
    (hepsilonH : epsilonH ≠ 0) :
    localIWCarrier epsilonH omega ≠ 0 := by
  unfold localIWCarrier
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hcoef :
      omega / (8 * Real.pi) ≠ 0 :=
    div_ne_zero homega (mul_ne_zero (by norm_num) hpi)
  intro hzero
  exact hcoef ((smul_eq_zero.mp hzero).resolve_right hepsilonH)

theorem localIWResponse_unit
    (T : V →ₗ[ℝ] ℝ)
    (epsilonH : W)
    (omega : ℝ)
    (u : V)
    (hunit : T u = 1) :
    localIWResponse T epsilonH omega u =
      localIWCarrier epsilonH omega := by
  simp [hunit]

/-- The coefficient covector in the local response is unique and is exactly T. -/
theorem localIWResponse_coefficient_unique
    (T alpha : V →ₗ[ℝ] ℝ)
    (epsilonH : W)
    (omega : ℝ)
    (homega : omega ≠ 0)
    (hepsilonH : epsilonH ≠ 0)
    (halpha : ∀ v : V,
      localIWResponse T epsilonH omega v =
        (alpha v) • localIWCarrier epsilonH omega) :
    alpha = T := by
  exact rank_one_response_factorization_unique
    (localIWCarrier epsilonH omega)
    (localIWCarrier_nonzero epsilonH omega homega hepsilonH)
    (fun v => localIWResponse T epsilonH omega v)
    alpha T halpha
    (fun v => (localIWResponse_apply T epsilonH omega v).symm)

/-- The explicit pointwise response automatically supplies all fields previously packaged in
PointwiseClockResponseData. -/
noncomputable def explicitPointwiseClockResponseData
    (T : V →ₗ[ℝ] ℝ)
    (epsilonH : W)
    (omega : ℝ)
    (u : V)
    (homega : omega ≠ 0)
    (hepsilonH : epsilonH ≠ 0)
    (hunit : T u = 1) :
    PointwiseClockResponseData (V:=V) (W:=W) where
  response := fun v => localIWResponse T epsilonH omega v
  carrier := localIWCarrier epsilonH omega
  carrier_nonzero :=
    localIWCarrier_nonzero epsilonH omega homega hepsilonH
  lambda := T
  uhat := u
  factorization := by
    intro v
    exact localIWResponse_apply T epsilonH omega v
  unit_response :=
    localIWResponse_unit T epsilonH omega u hunit

end ExplicitLocalIW

section MetricExplicitLocalIW

variable {V W : Type*}
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [NoZeroSMulDivisors ℝ W]

variable (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- With T_O=-omega g(u,.), the local Iyer--Wald response coefficient is forced to be T_O. -/
theorem metricLocalIW_coefficient_forced
    (u : V)
    (epsilonH : W)
    (omega : ℝ)
    (homega : omega ≠ 0)
    (hu : B u u = -1)
    (hepsilonH : epsilonH ≠ 0)
    (alpha : V →ₗ[ℝ] ℝ)
    (halpha : ∀ v : V,
      localIWResponse
          (metricClockCovector B u omega)
          epsilonH omega v =
        (alpha v) • localIWCarrier epsilonH omega) :
    alpha = metricClockCovector B u omega := by
  exact localIWResponse_coefficient_unique
    (metricClockCovector B u omega)
    alpha epsilonH omega
    homega hepsilonH halpha

/-- The metric-normalized clock direction gives the required unit pointwise response
automatically. -/
theorem metricLocalIW_unit_response
    (u : V)
    (epsilonH : W)
    (omega : ℝ)
    (homega : omega ≠ 0)
    (hu : B u u = -1) :
    localIWResponse
        (metricClockCovector B u omega)
        epsilonH omega
        (metricClockUnit u omega) =
      localIWCarrier epsilonH omega := by
  apply localIWResponse_unit
  exact metricClockCovector_normalized B u omega homega hu

end MetricExplicitLocalIW

end RelativeRest
