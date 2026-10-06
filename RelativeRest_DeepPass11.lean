import RelativeRest_DeepPass10

/-!
# Relative Rest: deep forced pass 11

Derive the local clock covector directly from the metric normalization.

The manuscript does not choose a local covector independently:
  T_O = -omega u_*^flat,
  uhat_* = omega^{-1} u_*,
  g(u_*,u_*) = -1.
Therefore T_O(uhat_*)=1 is forced.  This file packages that statement as an actual linear map,
derives its kernel, quotient line, local lift, and reuses the self-adjoint carrier theorem with no
separately supplied local clock covector.
-/

noncomputable section

open Function Set

namespace RelativeRest

section MetricClock

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- T_O = -omega g(u,.) in the background metric. -/
def metricClockCovector
    (u : V) (omega : ℝ) : V →ₗ[ℝ] ℝ :=
  (-omega) • (B u)

@[simp] theorem metricClockCovector_apply
    (u v : V) (omega : ℝ) :
    metricClockCovector B u omega v =
      -omega * B u v := by
  rfl

/-- uhat = omega^{-1} u. -/
def metricClockUnit
    (u : V) (omega : ℝ) : V :=
  omega⁻¹ • u

/-- The clock covector is automatically normalized on the conformally unit clock direction. -/
theorem metricClockCovector_normalized
    (u : V) (omega : ℝ)
    (homega : omega ≠ 0)
    (hu : B u u = -1) :
    metricClockCovector B u omega
      (metricClockUnit u omega) = 1 := by
  simp [metricClockCovector, metricClockUnit, map_smul, hu, homega]
  field_simp [homega]

/-- Hence the metric-derived local clock covector is nonzero. -/
theorem metricClockCovector_nonzero
    (u : V) (omega : ℝ)
    (homega : omega ≠ 0)
    (hu : B u u = -1) :
    metricClockCovector B u omega ≠ 0 := by
  intro hzero
  have hnorm :=
    metricClockCovector_normalized B u omega homega hu
  rw [hzero] at hnorm
  simp at hnorm

/-- Its kernel is exactly the metric-orthogonal hyperplane to u. -/
theorem metricClockCovector_kernel_iff
    (u v : V) (omega : ℝ)
    (homega : omega ≠ 0) :
    metricClockCovector B u omega v = 0 ↔
      B u v = 0 := by
  simp only [metricClockCovector_apply]
  constructor
  · intro h
    have hcoef : -omega ≠ 0 := neg_ne_zero.mpr homega
    exact (mul_eq_zero.mp h).resolve_left hcoef
  · intro h
    rw [h]
    ring

/-- Every vector splits into its visible clock component plus an element of the invisible kernel. -/
theorem metricClock_decomposition
    (u v : V) (omega : ℝ)
    (homega : omega ≠ 0)
    (hu : B u u = -1) :
    metricClockCovector B u omega
      (v -
        (metricClockCovector B u omega v) •
          metricClockUnit u omega) = 0 := by
  simp [map_sub, map_smul,
    metricClockCovector_normalized B u omega homega hu]

/-- The metric-derived local clock quotient is canonically the real line. -/
noncomputable def metricClockLine
    (u : V) (omega : ℝ)
    (homega : omega ≠ 0)
    (hu : B u u = -1) :
    (V ⧸ LinearMap.ker
      (metricClockCovector B u omega)) ≃ₗ[ℝ] ℝ :=
  clockQuotientEquivReal
    (metricClockCovector B u omega)
    (metricClockCovector_nonzero B u omega homega hu)

/-- The local lift is no longer extra data: it is forced by the metric-derived covector and unit. -/
def metricClockLift
    (u : V) (omega : ℝ) : V →ₗ[ℝ] V :=
  normalizedClockMap
    (metricClockCovector B u omega)
    (metricClockUnit u omega)

@[simp] theorem metricClockLift_unit
    (u : V) (omega : ℝ)
    (homega : omega ≠ 0)
    (hu : B u u = -1) :
    metricClockLift B u omega
      (metricClockUnit u omega) =
      metricClockUnit u omega := by
  unfold metricClockLift
  rw [normalizedClockMap_apply]
  rw [metricClockCovector_normalized B u omega homega hu]
  simp

end MetricClock

/-! ## B. The self-adjoint carrier coefficient uses the forced metric clock covector -/

section MetricCarrier

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

theorem selfadjoint_carrier_forces_metric_clock
    (J : V →ₗ[ℝ] V)
    (u w v : V)
    (chi omega a : ℝ)
    (hsym : ∀ x y : V, B x y = B y x)
    (hself : ∀ x y : V, B x (J y) = B (J x) y)
    (hu : B u u = -1)
    (hJu : J u = chi • u)
    (hchi : chi = omega^2)
    (hw : B u w = 0)
    (hdecomp : J v = a • u + w) :
    a = omega * metricClockCovector B u omega v := by
  exact selfadjoint_carrier_forces_clock_coefficient
    B J u w v chi omega a
    (metricClockCovector B u omega)
    hsym hself hu hJu hchi
    (fun x => metricClockCovector_apply B u x omega)
    hw hdecomp

end MetricCarrier

end RelativeRest
