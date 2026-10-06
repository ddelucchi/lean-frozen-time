import RelativeRest_DeepPass26

/-!
# Relative Rest: deep forced pass 27

Prove uniqueness of the homogeneous clock-cover primitive as a one-form, not merely coefficientwise.

On the positive cover, take an arbitrary one-form
  theta = A(kappa) dTheta + B(kappa) dkappa.
If it has weight one under common scaling, is horizontal on the Euler field
D=kappa partial_kappa, and restricts to dTheta on the kappa=1 section, then necessarily
  A(kappa)=kappa, B(kappa)=0,
hence theta=kappa dTheta.

This is the exact finite-dimensional homogeneous/contact statement used in the manuscript.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-- General coordinate one-form on the two-dimensional clock cover. -/
def generalClockCoverForm
    (A B : ℝ → ℝ)
    (p v : R2) : ℝ :=
  A p.2 * v.1 + B p.2 * v.2

/-- Weight-one homogeneity of the whole one-form forces weight-one homogeneity of A. -/
theorem clockCoverForm_forces_A_homogeneous
    (A B : ℝ → ℝ)
    (hhom : ∀ c κ : ℝ, 0 < c → 0 < κ →
      generalClockCoverForm A B
          (clockScale c (0, κ))
          (clockScaleTangent c dThetaVec) =
        c * generalClockCoverForm A B (0, κ) dThetaVec) :
    ∀ c κ : ℝ, 0 < c → 0 < κ →
      A (c * κ) = c * A κ := by
  intro c κ hc hκ
  have h := hhom c κ hc hκ
  simpa [generalClockCoverForm, clockScale,
    clockScaleTangent, dThetaVec] using h

/-- Horizontality on the positive Euler/dilation field forces the dkappa coefficient to vanish. -/
theorem clockCoverForm_horizontality_forces_B_zero
    (A B : ℝ → ℝ)
    (hhoriz : ∀ κ : ℝ, 0 < κ →
      generalClockCoverForm A B
          (0, κ) (clockDilation (0, κ)) = 0) :
    ∀ κ : ℝ, 0 < κ → B κ = 0 := by
  intro κ hκ
  have h := hhoriz κ hκ
  simp [generalClockCoverForm, clockDilation] at h
  exact (mul_eq_zero.mp h).resolve_right (ne_of_gt hκ)

/-- Unit-section normalization fixes A(1)=1. -/
theorem clockCoverForm_section_normalization
    (A B : ℝ → ℝ)
    (hsection :
      generalClockCoverForm A B (0, 1) dThetaVec = 1) :
    A 1 = 1 := by
  simpa [generalClockCoverForm, dThetaVec] using hsection

/-- The homogeneous, horizontal, normalized clock-cover primitive is uniquely kappa dTheta. -/
theorem clockCoverForm_unique
    (A B : ℝ → ℝ)
    (hhom : ∀ c κ : ℝ, 0 < c → 0 < κ →
      generalClockCoverForm A B
          (clockScale c (0, κ))
          (clockScaleTangent c dThetaVec) =
        c * generalClockCoverForm A B (0, κ) dThetaVec)
    (hhoriz : ∀ κ : ℝ, 0 < κ →
      generalClockCoverForm A B
          (0, κ) (clockDilation (0, κ)) = 0)
    (hsection :
      generalClockCoverForm A B (0, 1) dThetaVec = 1)
    (κ : ℝ) (hκ : 0 < κ) :
    A κ = κ ∧ B κ = 0 := by
  have hAhom :=
    clockCoverForm_forces_A_homogeneous A B hhom
  have hAone :=
    clockCoverForm_section_normalization A B hsection
  have hB :=
    clockCoverForm_horizontality_forces_B_zero A B hhoriz κ hκ
  constructor
  · have h :=
      homogeneous_conformal_factor A hAhom κ hκ
    rw [h, hAone, one_mul]
  · exact hB

/-- Therefore the value of any admissible primitive agrees with the canonical clock one-form at
every positive-cover point. -/
theorem clockCoverForm_eq_canonical
    (A B : ℝ → ℝ)
    (hhom : ∀ c κ : ℝ, 0 < c → 0 < κ →
      generalClockCoverForm A B
          (clockScale c (0, κ))
          (clockScaleTangent c dThetaVec) =
        c * generalClockCoverForm A B (0, κ) dThetaVec)
    (hhoriz : ∀ κ : ℝ, 0 < κ →
      generalClockCoverForm A B
          (0, κ) (clockDilation (0, κ)) = 0)
    (hsection :
      generalClockCoverForm A B (0, 1) dThetaVec = 1)
    (theta κ : ℝ) (hκ : 0 < κ)
    (v : R2) :
    generalClockCoverForm A B (theta, κ) v =
      clockThetaForm (theta, κ) v := by
  rcases clockCoverForm_unique
      A B hhom hhoriz hsection κ hκ with
    ⟨hA, hB⟩
  simp [generalClockCoverForm, clockThetaForm, hA, hB]

/-- The unique primitive is the contraction of the canonical clock symplectic form with the
Euler field and has the canonical bracket orientation. -/
theorem forced_clock_cover_certificate
    (A B : ℝ → ℝ)
    (hhom : ∀ c κ : ℝ, 0 < c → 0 < κ →
      generalClockCoverForm A B
          (clockScale c (0, κ))
          (clockScaleTangent c dThetaVec) =
        c * generalClockCoverForm A B (0, κ) dThetaVec)
    (hhoriz : ∀ κ : ℝ, 0 < κ →
      generalClockCoverForm A B
          (0, κ) (clockDilation (0, κ)) = 0)
    (hsection :
      generalClockCoverForm A B (0, 1) dThetaVec = 1)
    (theta κ : ℝ) (hκ : 0 < κ)
    (v : R2) :
    generalClockCoverForm A B (theta, κ) v =
        clockOmega (clockDilation (theta, κ)) v ∧
    clockOmega dKappaVec dThetaVec = 1 := by
  constructor
  · rw [clockCoverForm_eq_canonical
      A B hhom hhoriz hsection theta κ hκ v]
    exact (clockOmega_contract_dilation (theta, κ) v).symm
  · exact clockOmega_coordinates.1

end RelativeRest
