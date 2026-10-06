import RelativeRest_OneFile_Certificate

/-!
# Relative Rest: deep forced pass 2

This layer pushes several manuscript implications one step closer to their stated form without
pretending that the still-missing differential-geometric/Iyer--Wald infrastructure has already
been reconstructed.

The new results formalize:
* the unique action-to-optical boost intertwiner in the normalized two-dimensional modules;
* derivation of the characteristic clock covector from the Iyer--Wald response equation, rather
  than supplying the covector and its factorization as independent data;
* the normalized one-dimensional local/global clock identification;
* exactness forcing the synchronization correction differential;
* uniqueness of the homogeneous clock-cover coefficients;
* the algebraic condition under which boost balance is exactly zero timelike/radial response.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-! ## A. Forced action-to-optical intertwiner -/

def TO : R2 := (1, 0)
def RO : R2 := (0, 1)
def BO (v : R2) : R2 := (v.2, v.1)
def JA (v : R2) : R2 := (v.2, v.1)
def JO (v : R2) : R2 := (v.1, -v.2)

def actionToOptical (v : R2) : R2 :=
  ((v.1 + v.2) / 2, (v.2 - v.1) / 2)

@[simp] theorem BO_TO : BO TO = RO := by
  ext <;> norm_num [BO, TO, RO]

@[simp] theorem BO_RO : BO RO = TO := by
  ext <;> norm_num [BO, TO, RO]

@[simp] theorem actionToOptical_CA : actionToOptical CA = TO := by
  ext <;> norm_num [actionToOptical, CA, TO]

@[simp] theorem actionToOptical_DA : actionToOptical DA = RO := by
  ext <;> norm_num [actionToOptical, DA, RO]

theorem actionToOptical_intertwines_generator (v : R2) :
    actionToOptical (YA v) = BO (actionToOptical v) := by
  rcases v with ⟨x, y⟩
  ext <;> simp [actionToOptical, YA, BO] <;> ring

theorem actionToOptical_intertwines_exchange (v : R2) :
    actionToOptical (JA v) = JO (actionToOptical v) := by
  rcases v with ⟨x, y⟩
  ext <;> simp [actionToOptical, JA, JO] <;> ring

def opticalBoost (s : ℝ) (v : R2) : R2 :=
  (Real.cosh s * v.1 + Real.sinh s * v.2,
   Real.sinh s * v.1 + Real.cosh s * v.2)

theorem actionToOptical_intertwines_boost (s : ℝ) (v : R2) :
    actionToOptical (actionBoost s v) = opticalBoost s (actionToOptical v) := by
  rcases v with ⟨x, y⟩
  apply Prod.ext <;>
    simp [actionToOptical, actionBoost, opticalBoost,
      ← Real.cosh_add_sinh, ← Real.cosh_sub_sinh] <;> ring

theorem normalized_relative_rest_certificate (s : ℝ) :
    (Real.exp (-s) = Real.exp s) ↔
    ((Real.exp s - Real.exp (-s)) /
      (Real.exp s + Real.exp (-s)) = 0) := by
  rw [action_rest_iff_zero]
  rw [optical_defect_is_tanh, optical_rest_iff_zero]

/-! ## B. Derive the characteristic clock covector from the response equation -/

section IyerWaldForced

variable {P K : Type*}
  [AddCommGroup P] [Module ℝ P]
  [AddCommGroup K] [Module ℝ K]

structure IyerWaldResponseData where
  beta : P →ₗ[ℝ] K
  ell : P →ₗ[ℝ] ℝ
  omegaY : K →ₗ[ℝ] ℝ
  beta_surj : Function.Surjective beta
  bridge : ∀ p : P, omegaY (beta p) = -2 * ell p
  ell_nonzero : ell ≠ 0

def lambdaFromOmega (D : IyerWaldResponseData (P:=P) (K:=K)) : K →ₗ[ℝ] ℝ :=
  (-1 / 2 : ℝ) • D.omegaY

theorem iyerWald_factorization (D : IyerWaldResponseData (P:=P) (K:=K)) :
    (lambdaFromOmega D).comp D.beta = D.ell := by
  ext p
  change (-1 / 2 : ℝ) * D.omegaY (D.beta p) = D.ell p
  rw [D.bridge p]
  ring

theorem iyerWald_lambda_unique
    (D : IyerWaldResponseData (P:=P) (K:=K))
    (Λ : K →ₗ[ℝ] ℝ)
    (hΛ : Λ.comp D.beta = D.ell) :
    Λ = lambdaFromOmega D := by
  exact descended_covector_unique D.beta D.beta_surj D.ell Λ
    (lambdaFromOmega D) hΛ (iyerWald_factorization D)

theorem iyerWald_lambda_nonzero
    (D : IyerWaldResponseData (P:=P) (K:=K)) :
    lambdaFromOmega D ≠ 0 := by
  intro hzero
  apply D.ell_nonzero
  have hfac := iyerWald_factorization D
  rw [hzero] at hfac
  simpa using hfac.symm

noncomputable def iyerWaldClockLine
    (D : IyerWaldResponseData (P:=P) (K:=K)) :
    (K ⧸ LinearMap.ker (lambdaFromOmega D)) ≃ₗ[ℝ] ℝ :=
  clockQuotientEquivReal (lambdaFromOmega D) (iyerWald_lambda_nonzero D)

theorem iyerWald_unit_exists
    (D : IyerWaldResponseData (P:=P) (K:=K)) :
    ∃ X : K, lambdaFromOmega D X = 1 := by
  exact (nonzero_covector_surjective (lambdaFromOmega D)
    (iyerWald_lambda_nonzero D)) 1

theorem iyerWald_units_differ_by_kernel
    (D : IyerWaldResponseData (P:=P) (K:=K))
    (X Y : K)
    (hX : lambdaFromOmega D X = 1)
    (hY : lambdaFromOmega D Y = 1) :
    X - Y ∈ LinearMap.ker (lambdaFromOmega D) := by
  rw [LinearMap.mem_ker]
  simp [hX, hY]

end IyerWaldForced

/-! ## C. Forced local/global normalized clock identification -/

section NormalizedClockIdentification

variable {L₁ L₂ : Type*}
  [AddCommGroup L₁] [Module ℝ L₁]
  [AddCommGroup L₂] [Module ℝ L₂]

theorem normalizedClockMap_preserves_covector
    (α : L₁ →ₗ[ℝ] ℝ) (β : L₂ →ₗ[ℝ] ℝ)
    (u₂ : L₂) (hβu : β u₂ = 1)
    (x : L₁) :
    β (normalizedClockMap α u₂ x) = α x := by
  rw [normalizedClockMap_apply]
  simp [hβu]

theorem normalizedClockMap_roundtrip_left
    (α : L₁ →ₗ[ℝ] ℝ) (β : L₂ →ₗ[ℝ] ℝ)
    (u₁ : L₁) (u₂ : L₂)
    (hβu : β u₂ = 1)
    (hspan₁ : ∀ x : L₁, x = (α x) • u₁)
    (x : L₁) :
    normalizedClockMap β u₁ (normalizedClockMap α u₂ x) = x := by
  rw [normalizedClockMap_apply, normalizedClockMap_apply]
  rw [map_smul, hβu, one_smul]
  exact (hspan₁ x).symm

theorem normalizedClockMap_roundtrip_right
    (α : L₁ →ₗ[ℝ] ℝ) (β : L₂ →ₗ[ℝ] ℝ)
    (u₁ : L₁) (u₂ : L₂)
    (hαu : α u₁ = 1)
    (hspan₂ : ∀ y : L₂, y = (β y) • u₂)
    (y : L₂) :
    normalizedClockMap α u₂ (normalizedClockMap β u₁ y) = y := by
  rw [normalizedClockMap_apply, normalizedClockMap_apply]
  rw [map_smul, hαu, one_smul]
  exact (hspan₂ y).symm

end NormalizedClockIdentification

/-! ## D. Exact synchronization forces the correction differential -/

section SynchronizationDifferential

variable {W Z : Type*}
  [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z]

theorem synchronization_differential_forced
    (d : W →ₗ[ℝ] Z)
    (dT TO β : W)
    (hsync : dT = TO + β)
    (hexact : d dT = 0) :
    d β = - d TO := by
  have hsum : d TO + d β = 0 := by
    rw [hsync, map_add] at hexact
    exact hexact
  exact eq_neg_of_add_eq_zero_left hsum

theorem synchronization_anholonomy_cancels
    (d : W →ₗ[ℝ] Z)
    (dT TO β : W)
    (hsync : dT = TO + β)
    (hexact : d dT = 0) :
    d TO + d β = 0 := by
  rw [hsync, map_add] at hexact
  exact hexact

end SynchronizationDifferential

/-! ## E. Homogeneous clock-cover coefficients are unique -/

theorem clock_cover_coefficients_forced
    (A B : ℝ → ℝ)
    (hAhom : ∀ c κ : ℝ, 0 < c → 0 < κ → A (c * κ) = c * A κ)
    (hAone : A 1 = 1)
    (κ : ℝ) (hκ : 0 < κ)
    (hhoriz : κ * B κ = 0) :
    A κ = κ ∧ B κ = 0 := by
  constructor
  · have hlin := homogeneous_conformal_factor A hAhom κ hκ
    rw [hlin, hAone, one_mul]
  · exact (mul_eq_zero.mp hhoriz).resolve_left (ne_of_gt hκ)

/-! ## F. Balance versus zero timelike/radial response -/

def boostedMinus (qm σ : ℝ) : ℝ := Real.exp (-σ) * qm
def boostedPlus (qp σ : ℝ) : ℝ := Real.exp σ * qp
def timelikeResponse (qm qp σ : ℝ) : ℝ :=
  boostedMinus qm σ + boostedPlus qp σ

theorem boosted_response_product
    (qm qp σ : ℝ) :
    boostedMinus qm σ * boostedPlus qp σ = qm * qp := by
  unfold boostedMinus boostedPlus
  calc
    (Real.exp (-σ) * qm) * (Real.exp σ * qp)
        = (Real.exp (-σ) * Real.exp σ) * (qm * qp) := by ring
    _ = qm * qp := by
      rw [← Real.exp_add]
      simp

theorem boost_balance_iff_zero_timelike_response
    (qm qp σ : ℝ)
    (hopposite : qm * qp < 0) :
    boostDefect qm qp σ = 0 ↔ timelikeResponse qm qp σ = 0 := by
  let a : ℝ := boostedMinus qm σ
  let b : ℝ := boostedPlus qp σ
  have hab : a * b < 0 := by
    dsimp [a, b]
    rw [boosted_response_product qm qp σ]
    exact hopposite
  have hsquares :
      boostDefect qm qp σ = a^2 - b^2 := by
    unfold boostDefect
    rcases boosted_component_squares qm qp σ with ⟨hm, hp⟩
    dsimp [a, b]
    rw [hm, hp]
  constructor
  · intro hbal
    have hsq : a^2 = b^2 := by
      rw [hsquares] at hbal
      linarith
    have hsum : a + b = 0 := by
      nlinarith
    simpa [timelikeResponse, a, b] using hsum
  · intro hzero
    have hsum : a + b = 0 := by
      simpa [timelikeResponse, a, b] using hzero
    have hsq : a^2 = b^2 := by
      nlinarith
    rw [hsquares]
    linarith

theorem sigmaStar_zero_timelike_response
    (qm qp : ℝ)
    (hqm : qm ≠ 0) (hqp : qp ≠ 0)
    (hopposite : qm * qp < 0) :
    timelikeResponse qm qp (sigmaStar qm qp) = 0 := by
  exact (boost_balance_iff_zero_timelike_response
    qm qp (sigmaStar qm qp) hopposite).mp
      (sigmaStar_is_root qm qp hqm hqp)

end RelativeRest
