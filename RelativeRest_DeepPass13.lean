import RelativeRest_DeepPass12

/-!
# Relative Rest: deep forced pass 13

Close two manuscript-level logical gaps without adding geometric data:

1. lift the solution-preserving relative fixed point from a scalar component to the complete
   pointwise Einstein--Maxwell tensor residual;
2. strengthen the null-exchange closure from orthogonality/equal norms to the exact normalized
   Lorentzian metric on the radar two-plane.

The tensor theorem uses only the on-shell Einstein equation and nonvanishing Maxwell stress.
The optical theorem uses only the two null eikonal equations and the already-forced unit clock
normalization.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-! ## A. Full tensor fixed point -/

/-- A nonzero pointwise rank-two tensor has a nonzero component in the chosen frame. -/
theorem tensor44_nonzero_has_component
    (T : Tensor44)
    (hT : T ≠ 0) :
    ∃ i j : Fin 4, T i j ≠ 0 := by
  by_contra h
  push_neg at h
  apply hT
  funext i j
  exact h i j

/-- On shell, the full tensor residual vanishes at the relative fixed point. -/
theorem tensorRelativeResidual_onShell_zero
    (G T : Tensor44)
    (hEinstein : ∀ i j, G i j = 8 * Real.pi * T i j) :
    tensorRelativeResidual G T 0 = 0 := by
  rw [tensorRelativeResidual_onShell_eq_tensorDefect G T hEinstein 0]
  exact tensorDefect_zero T

/-- For nonzero Maxwell stress, preservation of the complete pointwise Einstein--Maxwell
equation forces the unique relative fixed point s=0. -/
theorem tensorRelativeResidual_zero_iff_fixed_point
    (G T : Tensor44)
    (hEinstein : ∀ i j, G i j = 8 * Real.pi * T i j)
    (hT : T ≠ 0)
    (s : ℝ) :
    tensorRelativeResidual G T s = 0 ↔ s = 0 := by
  constructor
  · intro hzero
    obtain ⟨i, j, hij⟩ := tensor44_nonzero_has_component T hT
    have hcomp : relativeResidual (G i j) (T i j) s = 0 := by
      have h := congrFun (congrFun hzero i) j
      simpa [tensorRelativeResidual] using h
    exact
      (relativeResidual_zero_iff_fixed_point
        (G i j) (T i j) s (hEinstein i j) hij).mp hcomp
  · rintro rfl
    exact tensorRelativeResidual_onShell_zero G T hEinstein

/-- Every odd tensor normal derivative is literally the first tensor jet componentwise. -/
theorem tensorDefect_odd_iteratedDeriv_eq_first
    (T : Tensor44)
    (i j : Fin 4)
    (n : ℕ) :
    iteratedDeriv (2 * n + 1)
        (fun s => tensorDefect T s i j) 0 =
      iteratedDeriv 1
        (fun s => tensorDefect T s i j) 0 := by
  rw [tensorDefect_odd_iteratedDeriv_carrier T i j n]
  simpa using tensorDefect_odd_iteratedDeriv_carrier T i j 0

/-! ## B. Null exchange forces the normalized optical plane -/

section OpticalMetricClosure

variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)

/-- Two null eikonals T+R and T-R, together with the already fixed unit clock norm,
force T and R to be an orthonormal Lorentzian pair. -/
theorem null_pair_unit_radar_frame
    (hsym : ∀ x y, bil B x y = bil B y x)
    (T R : W)
    (hplus : bil B (T + R) (T + R) = 0)
    (hminus : bil B (T - R) (T - R) = 0)
    (hTunit : bil B T T = -1) :
    bil B T R = 0 ∧ bil B R R = 1 := by
  constructor
  · exact null_pair_orthogonal B hsym T R hplus hminus
  · have hnorm :=
      null_pair_equal_opposite_norm B hsym T R hplus hminus
    rw [hTunit] at hnorm
    simpa using hnorm

/-- In the forced radar basis, the bilinear form is exactly diag(-1,+1). -/
theorem radar_plane_metric
    (hsym : ∀ x y, bil B x y = bil B y x)
    (T R : W)
    (hTT : bil B T T = -1)
    (hTR : bil B T R = 0)
    (hRR : bil B R R = 1)
    (a b : ℝ) :
    bil B (a • T + b • R) (a • T + b • R) =
      -a^2 + b^2 := by
  have hRT : bil B R T = 0 := by
    rw [hsym R T]
    exact hTR
  simp only [bil, map_add, map_smul, LinearMap.add_apply]
  rw [hTT, hTR, hRT, hRR]
  ring

/-- Therefore the manuscript's local optical closure is forced by null exchange plus clock
normalization: no independent two-metric remains on the radar plane. -/
theorem null_eikonals_force_optical_metric
    (hsym : ∀ x y, bil B x y = bil B y x)
    (T R : W)
    (hplus : bil B (T + R) (T + R) = 0)
    (hminus : bil B (T - R) (T - R) = 0)
    (hTunit : bil B T T = -1)
    (a b : ℝ) :
    bil B (a • T + b • R) (a • T + b • R) =
      -a^2 + b^2 := by
  rcases
      null_pair_unit_radar_frame B hsym T R hplus hminus hTunit with
    ⟨hTR, hRR⟩
  exact radar_plane_metric B hsym T R hTunit hTR hRR a b

end OpticalMetricClosure

end RelativeRest
