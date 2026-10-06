import RelativeRest_DeepPass8

/-!
# Relative Rest: deep forced pass 9

This layer isolates the exact Einstein--Maxwell content of the Iyer--Wald bridge.

The general Iyer--Wald variational identity is a standard external theorem of covariant phase
space.  What is specific to this paper is the response of the Einstein--Maxwell constraint under
the relative action scaling.  Here that response is proved componentwise and then contracted,
giving exactly the coefficient used in the manuscript:
  (1/8pi) eps_a J^a_b xi^b = -2 eps_a T^a_b xi^b.

The file also formalizes exactness/normalization of a one-dimensional clock covector and the
corresponding Reeb uniqueness.
-/

noncomputable section

open Function Set
open scoped BigOperators

namespace RelativeRest

abbrev Tensor44 := Fin 4 → Fin 4 → ℝ
abbrev Vec4 := Fin 4 → ℝ

/-! ## A. Pointwise Einstein--Maxwell relative defect -/

def tensorDefect (T : Tensor44) (s : ℝ) : Tensor44 :=
  fun i j => -16 * Real.pi * Real.sinh s * T i j

theorem tensorDefect_zero
    (T : Tensor44) :
    tensorDefect T 0 = 0 := by
  funext i j
  simp [tensorDefect]

/-- Every component of the fixed-point normal is -16 pi times the Maxwell stress. -/
theorem tensorDefect_hasDerivAt_zero
    (T : Tensor44) (i j : Fin 4) :
    HasDerivAt (fun s => tensorDefect T s i j)
      (-16 * Real.pi * T i j) 0 := by
  simpa [tensorDefect] using defect_hasDerivAt_zero (T i j)

/-- The fixed-point jet tensor. -/
def tensorJet (T : Tensor44) : Tensor44 :=
  fun i j => -16 * Real.pi * T i j

@[simp] theorem tensorJet_apply
    (T : Tensor44) (i j : Fin 4) :
    tensorJet T i j = -16 * Real.pi * T i j := rfl

/-! ## B. Stress/jet contraction used by the bridge -/

/-- Algebraic stand-in for eps_a A^a_b xi^b at one spacetime point. -/
def tensorContraction
    (eps xi : Vec4)
    (A : Tensor44) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, eps i * A i j * xi j

theorem tensorContraction_smul
    (eps xi : Vec4)
    (A : Tensor44)
    (c : ℝ) :
    tensorContraction eps xi (fun i j => c * A i j) =
      c * tensorContraction eps xi A := by
  unfold tensorContraction
  simp_rw [mul_assoc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The manuscript's pointwise bridge coefficient follows exactly from J=-16 pi T. -/
theorem jet_contraction_eq_minus_two_stress
    (eps xi : Vec4)
    (T : Tensor44) :
    (1 / (8 * Real.pi)) *
      tensorContraction eps xi (tensorJet T) =
      -2 * tensorContraction eps xi T := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hscale :
      tensorContraction eps xi (tensorJet T) =
        (-16 * Real.pi) * tensorContraction eps xi T := by
    change tensorContraction eps xi
      (fun i j => (-16 * Real.pi) * T i j) =
      (-16 * Real.pi) * tensorContraction eps xi T
    exact tensorContraction_smul eps xi T (-16 * Real.pi)
  rw [hscale]
  field_simp [hpi]
  ring

/-- If the Einstein--Maxwell trace equation gives Ric=8 pi T componentwise, then the same jet is
-2 Ric componentwise. -/
theorem tensorJet_eq_minus_two_Ricci
    (T Ric : Tensor44)
    (hRic : ∀ i j, Ric i j = 8 * Real.pi * T i j) :
    tensorJet T = fun i j => -2 * Ric i j := by
  funext i j
  simp only [tensorJet]
  rw [hRic i j]
  ring

/-! ## C. One-dimensional clock covectors are exact and fix the Reeb direction -/

section OneDimensionalPrimitive

/-- A linear covector on the real clock line has the canonical linear primitive. -/
def linePrimitive (lambda : ℝ →ₗ[ℝ] ℝ) (theta : ℝ) : ℝ :=
  lambda theta

theorem linePrimitive_hasDerivAt
    (lambda : ℝ →ₗ[ℝ] ℝ)
    (theta : ℝ) :
    HasDerivAt (linePrimitive lambda)
      (lambda 1) theta := by
  have hlin : ∀ x : ℝ, lambda x = x * lambda 1 := by
    intro x
    calc
      lambda x = lambda (x • (1 : ℝ)) := by simp
      _ = x • lambda 1 := by rw [map_smul]
      _ = x * lambda 1 := by simp [smul_eq_mul]
  have hfun :
      linePrimitive lambda = fun x : ℝ => x * lambda 1 := by
    funext x
    exact hlin x
  rw [hfun]
  simpa [mul_comm] using
    (hasDerivAt_id theta).mul_const (lambda 1)

/-- A normalized one-dimensional clock covector therefore has unit clock derivative. -/
theorem normalized_linePrimitive_hasDerivAt
    (lambda : ℝ →ₗ[ℝ] ℝ)
    (hnorm : lambda 1 = 1)
    (theta : ℝ) :
    HasDerivAt (linePrimitive lambda) 1 theta := by
  simpa [hnorm] using linePrimitive_hasDerivAt lambda theta

/-- On a one-dimensional clock line, the Reeb condition lambda(R)=1 has a unique solution once
lambda is normalized on the chosen positive unit. -/
theorem oneDimensional_Reeb_unique
    (lambda : ℝ →ₗ[ℝ] ℝ)
    (hnorm : lambda 1 = 1)
    (R : ℝ)
    (hR : lambda R = 1) :
    R = 1 := by
  have hlin : lambda R = R * lambda 1 := by
    calc
      lambda R = lambda (R • (1 : ℝ)) := by simp
      _ = R • lambda 1 := by rw [map_smul]
      _ = R * lambda 1 := by simp [smul_eq_mul]
  rw [hlin, hnorm, mul_one] at hR
  exact hR

end OneDimensionalPrimitive

/-! ## D. Four-dimensional two-form conformal weight -/

/-- Conformal Hodge weight D-2p for p-forms under g -> Omega^2 g. -/
def hodgeConformalWeight (D p : ℤ) : ℤ :=
  D - 2 * p

theorem hodgeWeight_twoForm_fourDim :
    hodgeConformalWeight 4 2 = 0 := by
  norm_num [hodgeConformalWeight]

/-- Thus any conformal Hodge scaling law with weight Omega^(D-2p) has unit exponent for two-forms
in four dimensions. -/
theorem fourDim_twoForm_hodge_scale_exponent
    (Omega : ℝ) :
    Omega ^ (Int.natAbs (hodgeConformalWeight 4 2)) = 1 := by
  norm_num [hodgeConformalWeight]

end RelativeRest
