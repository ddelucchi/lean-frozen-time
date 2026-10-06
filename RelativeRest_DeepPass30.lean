import RelativeRest_DeepPass29

/-!
# Relative Rest: deep forced pass 30

Derive the local clock covector from the conformally normalized metric itself.

If g(u,u)=-1, chi=omega^2, ghat=chi g, and uhat=omega^{-1}u, then uhat is automatically
unit timelike for ghat and
  -ghat(uhat,.) = -omega g(u,.) = T_O.
Thus the local clock covector is simultaneously the ghat-metric dual of the normalized observer
and the background metric covector used in the manuscript.
-/

noncomputable section

open Function Set

namespace RelativeRest

section ChronometricMetric

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- Conformal chronometric bilinear form ghat=chi g. -/
def chronometricMetric
    (chi : ℝ) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  chi • B

@[simp] theorem chronometricMetric_apply
    (chi : ℝ)
    (v w : V) :
    chronometricMetric B chi v w =
      chi * B v w := by
  rfl

/-- uhat=omega^{-1}u is unit timelike for ghat=omega^2 g. -/
theorem chronometricMetric_unit_observer
    (u : V)
    (chi omega : ℝ)
    (homega : omega ≠ 0)
    (hchi : chi = omega^2)
    (hu : B u u = -1) :
    chronometricMetric B chi
        (metricClockUnit u omega)
        (metricClockUnit u omega) = -1 := by
  simp [chronometricMetric, metricClockUnit,
    map_smul, hchi, hu]
  field_simp [homega]
  ring

/-- The negative ghat-metric dual of uhat is exactly the background expression
-omega g(u,.). -/
theorem chronometricMetric_dual_eq_metricClockCovector
    (u : V)
    (chi omega : ℝ)
    (homega : omega ≠ 0)
    (hchi : chi = omega^2) :
    (-1 : ℝ) •
        (chronometricMetric B chi
          (metricClockUnit u omega)) =
      metricClockCovector B u omega := by
  ext v
  simp [chronometricMetric, metricClockUnit,
    metricClockCovector, map_smul, hchi]
  field_simp [homega]
  ring

/-- Hence the chronometric metric dual is normalized on the chronometric unit observer. -/
theorem chronometricMetric_clock_normalized
    (u : V)
    (chi omega : ℝ)
    (homega : omega ≠ 0)
    (hchi : chi = omega^2)
    (hu : B u u = -1) :
    ((-1 : ℝ) •
        (chronometricMetric B chi
          (metricClockUnit u omega)))
        (metricClockUnit u omega) = 1 := by
  rw [chronometricMetric_dual_eq_metricClockCovector
    B u chi omega homega hchi]
  exact metricClockCovector_normalized
    B u omega homega hu

/-- Complete localdata normalization certificate. -/
theorem local_chronometric_data_forced
    (u : V)
    (chi omega : ℝ)
    (homega : omega ≠ 0)
    (hchi : chi = omega^2)
    (hu : B u u = -1) :
    chronometricMetric B chi
        (metricClockUnit u omega)
        (metricClockUnit u omega) = -1 ∧
    ((-1 : ℝ) •
        (chronometricMetric B chi
          (metricClockUnit u omega))) =
      metricClockCovector B u omega ∧
    metricClockCovector B u omega
        (metricClockUnit u omega) = 1 := by
  exact
    ⟨chronometricMetric_unit_observer
        B u chi omega homega hchi hu,
      chronometricMetric_dual_eq_metricClockCovector
        B u chi omega homega hchi,
      metricClockCovector_normalized
        B u omega homega hu⟩

end ChronometricMetric

end RelativeRest
