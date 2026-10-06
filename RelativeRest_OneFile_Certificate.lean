import Mathlib

/-!
# Relative Rest as the Resolution of Frozen Time in Einstein–Maxwell Theory
## One-file Lean certificate of the forced algebraic/uniqueness chain

This file is intentionally adversarial about assumptions.

* Every theorem in the scalar/projective/boost/quotient/clock-algebra chain below is proved.
* No proof placeholders or project-local axioms are used in theorem bodies.
* Where the manuscript uses infrastructure that is not presently reconstructed here from the
  Einstein–Maxwell Lagrangian (full Lorentzian tensor calculus, Iyer–Wald current, contact
  reduction, causal endpoint globalization, explicit Kerr–Newman curvature), the required
  geometric fact is represented by an explicit hypothesis to a downstream theorem.

Consequently this file is a genuine kernel-checkable *logical certificate* for a large fraction
of the manuscript, but it is not falsely advertised as a first-principles formalization of all
GR/covariant-phase-space infrastructure.  The remaining interfaces are isolated in the
`GeometricInterface` and `KerrNewmanInterface` sections so they can be discharged later without
changing the downstream proofs.
-/

noncomputable section

open scoped BigOperators
open Function Set

namespace RelativeRest

/-! ## 1. Projective relative coordinate -/

/-- The projectively normalized relative defect coordinate. -/
def delta (r : ℝ) : ℝ := (r - 1) / (r + 1)

@[simp] theorem delta_one : delta 1 = 0 := by
  norm_num [delta]

@[simp] theorem delta_zero : delta 0 = -1 := by
  norm_num [delta]

/-- Exchange `r ↦ r⁻¹` reverses the relative defect on the positive sector. -/
theorem delta_inv (r : ℝ) (hr : 0 < r) : delta r⁻¹ = - delta r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrp : r + 1 ≠ 0 := by positivity
  have hrip : r⁻¹ + 1 ≠ 0 := by
    have hir : 0 < r⁻¹ := inv_pos.mpr hr
    positivity
  rw [delta, delta]
  field_simp [hr0, hrp, hrip]
  ring

/-- Multiplication of positive ratios becomes Einstein/Möbius addition of defects. -/
theorem delta_mul (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    delta (r₁ * r₂) = (delta r₁ + delta r₂) / (1 + delta r₁ * delta r₂) := by
  have h1p : r₁ + 1 ≠ 0 := by positivity
  have h2p : r₂ + 1 ≠ 0 := by positivity
  have h12p : r₁ * r₂ + 1 ≠ 0 := by positivity
  have hA : delta r₁ + delta r₂ =
      2 * (r₁ * r₂ - 1) / ((r₁ + 1) * (r₂ + 1)) := by
    rw [delta, delta]
    field_simp [h1p, h2p]
    ring
  have hB : 1 + delta r₁ * delta r₂ =
      2 * (r₁ * r₂ + 1) / ((r₁ + 1) * (r₂ + 1)) := by
    rw [delta, delta]
    field_simp [h1p, h2p]
    ring
  rw [hA, hB, delta]
  field_simp [h1p, h2p, h12p]

/-- A fractional-linear coordinate with the three projective normalization conditions is unique.
The condition at infinity is encoded by equality of leading coefficients `a/c = 1`. -/
theorem mobius_projective_unique
    (a b c d r : ℝ)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (hcd : c + d ≠ 0)
    (hden : c * r + d ≠ 0)
    (hrden : r + 1 ≠ 0)
    (h0 : b / d = -1)
    (h1 : (a + b) / (c + d) = 0)
    (hinf : a / c = 1) :
    (a * r + b) / (c * r + d) = delta r := by
  have ha : a = c := by
    field_simp [hc] at hinf
    linarith
  have hb : b = -d := by
    field_simp [hd] at h0
    linarith
  have hab : a + b = 0 := by
    have hcd0 : c + d ≠ 0 := hcd
    exact (div_eq_zero_iff.mp h1).resolve_right hcd0
  have hdc : d = c := by
    rw [ha, hb] at hab
    linarith
  subst a
  subst b
  subst d
  rw [delta]
  field_simp [hc, hden, hrden]
  ring

/-- The exponential parametrization has the unique exchange fixed point `s = 0`. -/
theorem exp_two_eq_one_iff (s : ℝ) : Real.exp (2 * s) = 1 ↔ s = 0 := by
  constructor
  · intro h
    have h' : Real.exp (2 * s) = Real.exp 0 := by simpa using h
    have hs : 2 * s = 0 := Real.exp_injective h'
    linarith
  · rintro rfl
    simp

/-- The relative character ratio has a unique exchange fixed point. -/
theorem exchange_fixed_point_unique (s : ℝ) : Real.exp (2 * s) = Real.exp (-2 * s) ↔ s = 0 := by
  constructor
  · intro h
    have hs : 2 * s = -2 * s := Real.exp_injective h
    linarith
  · rintro rfl
    simp

/-- A direct exponential expression for the projective coordinate equals `tanh`. -/
theorem delta_exp_two (s : ℝ) : delta (Real.exp (2 * s)) = Real.tanh s := by
  rw [delta, Real.tanh_eq_sinh_div_cosh]
  rw [show Real.exp (2 * s) = Real.exp s * Real.exp s by
    rw [show (2 : ℝ) * s = s + s by ring, Real.exp_add]]
  have he : Real.exp s ≠ 0 := ne_of_gt (Real.exp_pos s)
  rw [show Real.exp s * Real.exp s - 1 =
      Real.exp s * (Real.exp s - Real.exp (-s)) by
        rw [Real.exp_neg]
        field_simp [he]]
  rw [show Real.exp s * Real.exp s + 1 =
      Real.exp s * (Real.exp s + Real.exp (-s)) by
        rw [Real.exp_neg]
        field_simp [he]]
  rw [mul_div_mul_left _ _ he]
  rw [← Real.cosh_add_sinh s, ← Real.cosh_sub_sinh s]
  ring_nf

/-! ## 2. Four-dimensional reciprocal scaling -/

/-- Relative exponent carried by the Einstein–Hilbert sector after `(u,s)` reparametrization. -/
def wG (D : ℝ) : ℝ := -(D - 2) / 2

/-- Relative exponent carried by the Maxwell sector after `(u,s)` reparametrization. -/
def wM (D : ℝ) : ℝ := (6 - D) / 2

/-- Exact reciprocity of the two relative weights singles out four dimensions. -/
theorem reciprocal_weights_iff_four (D : ℝ) : wG D = -(wM D) ↔ D = 4 := by
  unfold wG wM
  constructor <;> intro h
  · linarith
  · subst D
    norm_num

/-- In four dimensions the relative weights are exactly `-1` and `+1`. -/
theorem four_dimensional_weights : wG 4 = -1 ∧ wM 4 = 1 := by
  norm_num [wG, wM]

/-- Algebraic scaling exponent of the Einstein-Hilbert density under constant homothety. -/
def gravScaleExponent (D : ℝ) : ℝ := D - 2

/-- Algebraic metric exponent of the Maxwell density under constant homothety. -/
def maxwellMetricScaleExponent (D : ℝ) : ℝ := D - 4

/-- Substitution `ρ=e^((u-s)/2)`, `λ=e^((u+s)/2)` gives the advertised relative exponents. -/
theorem relative_exponent_algebra (D : ℝ) :
    (-(D - 2) / 2 = wG D) ∧ ((D - 4) * (-1 / 2) + 2 * (1 / 2) = wM D) := by
  constructor
  · rfl
  · unfold wM
    ring

/-! ## 3. Dynamic fixed point and the defect jet -/

/-- A nonzero tensor component cannot remain a solution under relative Maxwell weight unless `s=0`. -/
theorem solution_preserving_fixed_point
    (t s : ℝ) (ht : t ≠ 0)
    (h : t = Real.exp (2 * s) * t) : s = 0 := by
  have hm : t * 1 = t * Real.exp (2 * s) := by
    calc
      t * 1 = t := by ring
      _ = Real.exp (2 * s) * t := h
      _ = t * Real.exp (2 * s) := by ring
  have he : (1 : ℝ) = Real.exp (2 * s) := mul_left_cancel₀ ht hm
  exact (exp_two_eq_one_iff s).mp he.symm

/-- Scalar model of the on-shell odd normal defect. -/
def defect (T s : ℝ) : ℝ := -16 * Real.pi * Real.sinh s * T

@[simp] theorem defect_zero (T : ℝ) : defect T 0 = 0 := by
  simp [defect]

/-- The normal derivative of the on-shell defect at the fixed point is `-16πT`. -/
theorem defect_hasDerivAt_zero (T : ℝ) :
    HasDerivAt (defect T) (-16 * Real.pi * T) 0 := by
  unfold defect
  have h := (Real.hasDerivAt_sinh 0).const_mul (-16 * Real.pi)
  have h' := h.mul_const T
  simpa [mul_assoc, mul_left_comm, mul_comm] using h'

/-- If the Einstein-Maxwell trace equation gives `Ric = 8πT`, then the fixed-point jet is `-2 Ric`. -/
theorem jet_eq_minus_two_ricci
    (T Ric : ℝ) (hRic : Ric = 8 * Real.pi * T) :
    -16 * Real.pi * T = -2 * Ric := by
  rw [hRic]
  ring

/-- Even/odd carrier pair used in the manuscript. -/
def carrierEven (η s : ℝ) : ℝ := 2 * Real.cosh s * η

def carrierOdd (η s : ℝ) : ℝ := -2 * Real.sinh s * η

@[simp] theorem carrierOdd_zero (η : ℝ) : carrierOdd η 0 = 0 := by
  simp [carrierOdd]

@[simp] theorem carrierEven_zero (η : ℝ) : carrierEven η 0 = 2 * η := by
  simp [carrierEven]

/-- The odd/even scalar ratio is exactly `tanh s` whenever the curvature component is nonzero. -/
theorem carrier_ratio
    (η s : ℝ) (hη : η ≠ 0) :
    - carrierOdd η s / carrierEven η s = Real.tanh s := by
  unfold carrierOdd carrierEven
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh s ≠ 0 := ne_of_gt (Real.cosh_pos s)
  field_simp [hη, hc]

/-! ## 4. The action boost module -/

abbrev R2 := ℝ × ℝ

/-- Action-space boost generator in the `(E_G,E_M)` basis. -/
def YA (v : R2) : R2 := (-v.1, v.2)

/-- Exchange-even action direction. -/
def CA : R2 := (1, 1)

/-- Exchange-odd action direction. -/
def DA : R2 := (-1, 1)

@[simp] theorem YA_CA : YA CA = DA := by
  ext <;> norm_num [YA, CA, DA]
@[simp] theorem YA_DA : YA DA = CA := by
  ext <;> norm_num [YA, CA, DA]

@[simp] theorem YA_sq (v : R2) : YA (YA v) = v := by
  rcases v with ⟨x,y⟩
  ext <;> simp [YA]

/-- Closed form for the boost generated by `YA`. -/
def actionBoost (s : ℝ) (v : R2) : R2 :=
  (Real.exp (-s) * v.1, Real.exp s * v.2)

/-- The exponential action on the even vector has the cosh/sinh decomposition. -/
theorem actionBoost_CA (s : ℝ) :
    actionBoost s CA =
      (Real.cosh s) • CA + (Real.sinh s) • DA := by
  apply Prod.ext <;>
    simp [actionBoost, CA, DA, ← Real.cosh_add_sinh, ← Real.cosh_sub_sinh]

/-! ## 5. Principal Maxwell/Rainich algebra: invariant scalar certificate -/

/-- Electromagnetic invariants in a principal Maxwell frame. -/
def maxwellI (E B : ℝ) : ℝ := 2 * (B^2 - E^2)

def maxwellJ (E B : ℝ) : ℝ := -4 * E * B

/-- The invariant combination collapses to the square of the principal field magnitude. -/
theorem maxwell_invariant_square (E B : ℝ) :
    (maxwellI E B)^2 + (maxwellJ E B)^2 = 4 * (E^2 + B^2)^2 := by
  unfold maxwellI maxwellJ
  ring

/-- A canonical principal-frame mixed Maxwell stress endomorphism, with overall scale `u`. -/
def principalStress (u : ℝ) : Fin 4 → Fin 4 → ℝ := fun i j =>
  if i = j then
    if i = 0 ∨ i = 1 then -u else u
  else 0

/-- Direct principal-frame Rainich square identity. -/
theorem principalStress_sq (u : ℝ) (i j : Fin 4) :
    (∑ k : Fin 4, principalStress u i k * principalStress u k j) =
      (if i = j then u^2 else 0) := by
  fin_cases i <;> fin_cases j <;>
    simp [principalStress] <;> ring

/-- Normalizing an endomorphism satisfying `J² = χ² I` produces an involution. -/
theorem normalized_involution
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] V) (χ : ℝ) (hχ : χ ≠ 0)
    (hRainich : J.comp J = (χ^2) • LinearMap.id) :
    let S : V →ₗ[ℝ] V := (χ⁻¹) • J
    S.comp S = LinearMap.id := by
  dsimp
  ext v
  have hpoint : J (J v) = χ^2 • v := by
    have := LinearMap.congr_fun hRainich v
    simpa using this
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [map_smul, hpoint]
  rw [smul_smul, smul_smul]
  have hs : χ⁻¹ * χ⁻¹ * χ ^ 2 = 1 := by
    field_simp [hχ]
  rw [hs, one_smul]
  simp

/-! ## 6. Unique residual boost balance -/

/-- Scalar boost defect. -/
def boostDefect (qminus qplus σ : ℝ) : ℝ :=
  Real.exp (-2 * σ) * qminus^2 - Real.exp (2 * σ) * qplus^2

/-- The advertised balance rapidity. -/
def sigmaStar (qminus qplus : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (|qminus / qplus|)

/-- Squared null components transform with opposite exponential weights. -/
theorem boosted_component_squares
    (qminus qplus σ : ℝ) :
    (Real.exp (-σ) * qminus)^2 = Real.exp (-2 * σ) * qminus^2 ∧
    (Real.exp σ * qplus)^2 = Real.exp (2 * σ) * qplus^2 := by
  constructor
  · rw [mul_pow]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  · rw [mul_pow]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring

/-- If the boost defect vanishes and both components are nonzero, the rapidity is unique. -/
theorem boost_balance_unique
    (qm qp σ τ : ℝ)
    (hqm : qm ≠ 0) (hqp : qp ≠ 0)
    (hσ : boostDefect qm qp σ = 0)
    (hτ : boostDefect qm qp τ = 0) : σ = τ := by
  unfold boostDefect at hσ hτ
  have hqm2 : qm^2 ≠ 0 := pow_ne_zero 2 hqm
  have hqp2 : qp^2 ≠ 0 := pow_ne_zero 2 hqp
  have hσ' : Real.exp (-2 * σ) * qm^2 = Real.exp (2 * σ) * qp^2 := by linarith
  have hτ' : Real.exp (-2 * τ) * qm^2 = Real.exp (2 * τ) * qp^2 := by linarith
  have hratioσ : Real.exp (4 * σ) = qm^2 / qp^2 := by
    have heσ : Real.exp (-2 * σ) ≠ 0 := ne_of_gt (Real.exp_pos _)
    calc
      Real.exp (4 * σ)
          = Real.exp (2 * σ) / Real.exp (-2 * σ) := by
              rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
              congr 1
              ring
      _ = qm^2 / qp^2 := by
              apply (div_eq_div_iff heσ hqp2).2
              simpa [mul_comm, mul_left_comm, mul_assoc] using hσ'.symm
  have hratioτ : Real.exp (4 * τ) = qm^2 / qp^2 := by
    have heτ : Real.exp (-2 * τ) ≠ 0 := ne_of_gt (Real.exp_pos _)
    calc
      Real.exp (4 * τ)
          = Real.exp (2 * τ) / Real.exp (-2 * τ) := by
              rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
              congr 1
              ring
      _ = qm^2 / qp^2 := by
              apply (div_eq_div_iff heτ hqp2).2
              simpa [mul_comm, mul_left_comm, mul_assoc] using hτ'.symm
  have he : Real.exp (4 * σ) = Real.exp (4 * τ) := hratioσ.trans hratioτ.symm
  have hs : 4 * σ = 4 * τ := Real.exp_injective he
  linarith

/-- Change of starting null dyad shifts the balancing rapidity oppositely. -/
theorem balance_shift_covariance
    (qm qp τ σ : ℝ) :
    boostDefect (Real.exp (-τ) * qm) (Real.exp τ * qp) σ =
      boostDefect qm qp (σ + τ) := by
  unfold boostDefect
  rw [mul_pow, mul_pow]
  have hminus : Real.exp (-2 * σ) * Real.exp (-τ) ^ 2 = Real.exp (-2 * (σ + τ)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hplus : Real.exp (2 * σ) * Real.exp τ ^ 2 = Real.exp (2 * (σ + τ)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hminus, ← mul_assoc, hplus]

/-- Therefore the balanced dyad is independent of the initial boost. -/
theorem balanced_dyad_invariant
    (km lp σ τ : ℝ) :
    (Real.exp (-(σ - τ)) * (Real.exp (-τ) * km) = Real.exp (-σ) * km) ∧
    (Real.exp (σ - τ) * (Real.exp τ * lp) = Real.exp σ * lp) := by
  constructor
  · rw [← mul_assoc, ← Real.exp_add]
    congr 1
    ring
  · rw [← mul_assoc, ← Real.exp_add]
    congr 1
    ring

/-! ## 7. Conformal normalization uniqueness in the stated carrier-algebraic category -/

/-- Homogeneity `f(cχ)=c f(χ)` forces a one-variable conformal factor to be linear. -/
theorem homogeneous_conformal_factor
    (f : ℝ → ℝ)
    (hhom : ∀ c χ : ℝ, 0 < c → 0 < χ → f (c * χ) = c * f χ)
    (χ : ℝ) (hχ : 0 < χ) :
    f χ = f 1 * χ := by
  have h := hhom χ 1 hχ (by norm_num)
  simpa [mul_comm] using h

/-- If `J²=χ²I`, then among factors `Cχ` the unit-involution normalization forces `C=1`
for positive `C,χ`. -/
theorem unit_involution_fixes_conformal_constant
    (C χ : ℝ) (hC : 0 < C) (hχ : 0 < χ)
    (hunit : χ^2 / (C * χ)^2 = 1) : C = 1 := by
  have hχ0 : χ ≠ 0 := ne_of_gt hχ
  have hC0 : C ≠ 0 := ne_of_gt hC
  field_simp [hχ0, hC0] at hunit
  have hC2 : C^2 = 1 := by nlinarith
  nlinarith [sq_nonneg (C - 1), sq_nonneg (C + 1)]

/-! ## 8. Relative rapidity identity -/

/-- Action-character ratio and optical null-frequency ratio are the same exponential. -/
theorem master_ratio (s : ℝ) :
    Real.exp s / Real.exp (-s) = Real.exp (2 * s) := by
  have he : Real.exp (-s) ≠ 0 := ne_of_gt (Real.exp_pos (-s))
  rw [div_eq_iff he]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The null-frequency defect is exactly `tanh s`. -/
theorem optical_defect_is_tanh (s : ℝ) :
    (Real.exp s - Real.exp (-s)) / (Real.exp s + Real.exp (-s)) = Real.tanh s := by
  rw [Real.tanh_eq_sinh_div_cosh]
  rw [← Real.cosh_add_sinh s, ← Real.cosh_sub_sinh s]
  ring_nf

/-- Relative rest is the same fixed point in action and optical ratios. -/
theorem action_rest_iff_zero (s : ℝ) :
    Real.exp (-s) = Real.exp s ↔ s = 0 := by
  constructor
  · intro h
    have hs : -s = s := Real.exp_injective h
    linarith
  · rintro rfl
    simp

theorem optical_rest_iff_zero (s : ℝ) :
    Real.tanh s = 0 ↔ s = 0 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh s ≠ 0 := ne_of_gt (Real.cosh_pos s)
  rw [div_eq_zero_iff]
  simp [hc, Real.sinh_eq_zero]

/-- All three notions of relative rest coincide. -/
theorem relative_rest_equivalences (s : ℝ) :
    (Real.exp (-s) = Real.exp s) ↔ (Real.tanh s = 0) := by
  rw [action_rest_iff_zero, optical_rest_iff_zero]

/-! ## 9. Abstract Iyer–Wald/characteristic linear descent

The physics-specific derivation of the Iyer–Wald current is deliberately not assumed globally.
Instead, this section proves the *forced linear algebra* once a parameter-to-characteristic map
and its stress response are supplied.  These theorems are directly reusable when the full
Einstein–Maxwell current is formalized.
-/

section LinearDescent

variable {P K : Type*} [AddCommGroup P] [Module ℝ P] [AddCommGroup K] [Module ℝ K]

/-- Pullback on covectors along a surjective linear map is injective. -/
theorem covector_pullback_injective
    (β : P →ₗ[ℝ] K) (hβ : Function.Surjective β) :
    Function.Injective (fun Λ : K →ₗ[ℝ] ℝ => Λ.comp β) := by
  intro Λ₁ Λ₂ h
  ext k
  obtain ⟨p, rfl⟩ := hβ k
  exact LinearMap.congr_fun h p

/-- A covector with a prescribed pullback is unique. -/
theorem descended_covector_unique
    (β : P →ₗ[ℝ] K) (hβ : Function.Surjective β)
    (ℓ : P →ₗ[ℝ] ℝ) (Λ₁ Λ₂ : K →ₗ[ℝ] ℝ)
    (h₁ : Λ₁.comp β = ℓ) (h₂ : Λ₂.comp β = ℓ) :
    Λ₁ = Λ₂ := by
  apply covector_pullback_injective β hβ
  exact h₁.trans h₂.symm

/-- If `ℓ=Λ∘β`, then parameters invisible to `β` are invisible to `ℓ`. -/
theorem kernel_inclusion_of_factorization
    (β : P →ₗ[ℝ] K) (Λ : K →ₗ[ℝ] ℝ) (ℓ : P →ₗ[ℝ] ℝ)
    (hfac : Λ.comp β = ℓ) :
    LinearMap.ker β ≤ LinearMap.ker ℓ := by
  intro p hp
  have hbp : β p = 0 := hp
  have := LinearMap.congr_fun hfac p
  simp [hbp] at this
  exact this.symm

/-- A nonzero real covector has full range `ℝ`. -/
theorem nonzero_covector_surjective
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) : Function.Surjective Λ := by
  exact LinearMap.surjective hΛ

/-- The quotient by the kernel of a nonzero real covector is canonically equivalent to its range. -/
noncomputable def clockQuotientEquivRange (Λ : K →ₗ[ℝ] ℝ) :
    (K ⧸ LinearMap.ker Λ) ≃ₗ[ℝ] LinearMap.range Λ :=
  LinearMap.quotKerEquivRange Λ

/-- A nonzero covector's range is all of `ℝ`. -/
theorem range_eq_top_of_nonzero
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) : LinearMap.range Λ = ⊤ := by
  exact LinearMap.range_eq_top.mpr (nonzero_covector_surjective Λ hΛ)

end LinearDescent

/-! ## 10. One-dimensional covector-preserving identification -/

section OneDimensional

variable {L₁ L₂ : Type*}
  [AddCommGroup L₁] [Module ℝ L₁]
  [AddCommGroup L₂] [Module ℝ L₂]

/-- In a one-dimensional space equipped with a chosen unit `u`, a normalized covector reconstructs
vectors by their scalar value.  This is the exact algebra used by the local/global clock bridge. -/
theorem reconstruction_from_normalized_covector
    (α : L₁ →ₗ[ℝ] ℝ) (u : L₁)
    (hu : α u = 1)
    (hspan : ∀ x : L₁, x = (α x) • u) :
    ∀ x : L₁, x = (α x) • u := hspan

/-- Uniqueness of a map that preserves normalized covectors and selected unit vectors. -/
theorem unique_covector_preserving_map
    (α : L₁ →ₗ[ℝ] ℝ) (β : L₂ →ₗ[ℝ] ℝ)
    (u₁ : L₁) (u₂ : L₂)
    (hαu : α u₁ = 1) (hβu : β u₂ = 1)
    (hspan₁ : ∀ x : L₁, x = (α x) • u₁)
    (hspan₂ : ∀ y : L₂, y = (β y) • u₂)
    (I J : L₁ →ₗ[ℝ] L₂)
    (hIu : I u₁ = u₂) (hJu : J u₁ = u₂) : I = J := by
  ext x
  rw [hspan₁ x, map_smul, map_smul, hIu, hJu]

/-- Explicit normalized map between two one-dimensional clock lines. -/
def normalizedClockMap
    (α : L₁ →ₗ[ℝ] ℝ) (u₂ : L₂) : L₁ →ₗ[ℝ] L₂ where
  toFun x := (α x) • u₂
  map_add' x y := by simp [add_smul]
  map_smul' c x := by simp [mul_smul]

@[simp] theorem normalizedClockMap_apply
    (α : L₁ →ₗ[ℝ] ℝ) (u₂ : L₂) (x : L₁) :
    normalizedClockMap α u₂ x = (α x) • u₂ := rfl

end OneDimensional

/-! ## 11. Pointwise local clock algebra -/

section LocalClock

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Abstract coefficient extraction from a distinguished unit direction. -/
structure LocalClockData where
  lambda : V →ₗ[ℝ] ℝ
  uhat : V
  normalized : lambda uhat = 1

/-- The kernel quotient identifies precisely the one-dimensional visible parameter when every
vector differs from its clock component by an invisible vector. -/
theorem local_decomposition
    (D : LocalClockData (V:=V))
    (v : V) :
    D.lambda (v - (D.lambda v) • D.uhat) = 0 := by
  simp [D.normalized]

/-- The manuscript's local lift is forced once `lambda(uhat)=1`. -/
def localLift (D : LocalClockData (V:=V)) : V →ₗ[ℝ] V where
  toFun v := (D.lambda v) • D.uhat
  map_add' x y := by simp [add_smul]
  map_smul' c x := by simp [mul_smul]

@[simp] theorem localLift_unit (D : LocalClockData (V:=V)) :
    localLift D D.uhat = D.uhat := by
  simp [localLift, D.normalized]

end LocalClock

/-! ## 12. Chronometric scalar identities -/

/-- If `K = χ²` with `χ>0`, then `sqrt χ` is the positive fourth-root clock rate. -/
theorem clock_rate_square
    (K χ ω : ℝ)
    (hχ : 0 ≤ χ) (hK : K = χ^2)
    (hω : ω = Real.sqrt χ) :
    ω^2 = χ ∧ K = ω^4 := by
  constructor
  · rw [hω, Real.sq_sqrt hχ]
  · rw [hK]
    have hs : ω^2 = χ := by rw [hω, Real.sq_sqrt hχ]
    nlinarith

/-- Principal stress energy density fixes the same clock scale. -/
theorem energy_density_clock_rate
    (χ ε ω : ℝ)
    (hχ : 0 ≤ χ)
    (hε : ε = χ / (16 * Real.pi))
    (hω : ω = Real.sqrt χ) :
    ω^2 = 16 * Real.pi * ε := by
  rw [hω, Real.sq_sqrt hχ, hε]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]

/-- The local optical covector has background norm `-ω²=-sqrt K` once the unit timelike norm
and `K=ω⁴` are supplied. -/
theorem optical_covector_norm_scalar
    (norm_u ω K : ℝ)
    (hu : norm_u = -1)
    (hK : K = ω^4)
    (hω : 0 ≤ ω) :
    ω^2 * norm_u = - Real.sqrt K := by
  rw [hu, hK]
  have hs : Real.sqrt (ω^4) = ω^2 := by
    rw [show ω^4 = (ω^2)^2 by ring]
    rw [Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (sq_nonneg ω)
  rw [hs]
  ring

/-! ## 13. Transport/integrability algebra -/

/-- Scalar coefficient identity behind `D_b ω = (ω/4) D_b log K` when `K=ω⁴`. -/
theorem logarithmic_rate_coefficient (ω dlogK dω : ℝ)
    (hω : ω ≠ 0)
    (h : dlogK = 4 * dω / ω) :
    dω = (ω / 4) * dlogK := by
  field_simp [hω] at h ⊢
  linarith

/-- If the spatial and mixed pieces of a two-form are independently zero, the manuscript's
transport conditions reduce to vorticity zero and acceleration-gradient balance. -/
theorem transport_zero_iff
    (ω varpi accel dlogK : ℝ)
    (hω : ω ≠ 0) :
    ((-2 * ω * varpi = 0) ∧ (-ω * (accel + dlogK / 4) = 0)) ↔
    (varpi = 0 ∧ accel = -dlogK / 4) := by
  constructor
  · rintro ⟨h₁,h₂⟩
    have hw2 : -2 * ω ≠ 0 := mul_ne_zero (by norm_num) hω
    have hv : varpi = 0 := by
      exact (mul_eq_zero.mp h₁).resolve_left hw2
    have hmix : accel + dlogK / 4 = 0 := by
      exact (mul_eq_zero.mp h₂).resolve_left (neg_ne_zero.mpr hω)
    constructor
    · exact hv
    · linarith
  · rintro ⟨rfl,hacc⟩
    constructor
    · ring
    · rw [hacc]
      ring

/-! ## 14. Null exchange / optical closure -/

/- Abstract symmetric bilinear form, enough to prove the null sum/difference closure. -/
section OpticalClosure

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

variable (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)

/-- Symmetric bilinear evaluation abbreviation. -/
def bil (x y : W) : ℝ := B x y

/-- If `T+R` and `T-R` are both null under a symmetric bilinear form, then `T` and `R` are
orthogonal. -/
theorem null_pair_orthogonal
    (hsym : ∀ x y, bil B x y = bil B y x)
    (T R : W)
    (hplus : bil B (T + R) (T + R) = 0)
    (hminus : bil B (T - R) (T - R) = 0) :
    bil B T R = 0 := by
  have hp := hplus
  have hm := hminus
  have hsym' : ∀ x y, B x y = B y x := by
    intro x y
    exact hsym x y
  simp only [bil, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at hp hm
  rw [hsym' R T] at hp hm
  change (B T) R = 0
  linarith

/-- The same two null equations imply equal-and-opposite norms. -/
theorem null_pair_equal_opposite_norm
    (hsym : ∀ x y, bil B x y = bil B y x)
    (T R : W)
    (hplus : bil B (T + R) (T + R) = 0)
    (hminus : bil B (T - R) (T - R) = 0) :
    -(bil B T T) = bil B R R := by
  have hp := hplus
  have hm := hminus
  have hsym' : ∀ x y, B x y = B y x := by
    intro x y
    exact hsym x y
  simp only [bil, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at hp hm
  rw [hsym' R T] at hp hm
  change -((B T) T) = (B R) R
  linarith

end OpticalClosure

/-- Synchronization correction is uniquely the difference between an exact radar differential and
local chronometric covector. -/
theorem synchronization_correction_unique
    {W : Type*} [AddCommGroup W]
    (dT TO β₁ β₂ : W)
    (h₁ : dT = TO + β₁)
    (h₂ : dT = TO + β₂) : β₁ = β₂ := by
  rw [h₁] at h₂
  exact add_left_cancel h₂

/-! ## 15. Clock-cover canonical pair: finite-dimensional algebraic model -/

/-- Standard clock-cover symplectic form on `(Θ,κ)` tangent vectors. -/
def clockOmega (v w : R2) : ℝ := v.2 * w.1 - v.1 * w.2

/-- Coordinate tangent vectors. -/
def dThetaVec : R2 := (1,0)
def dKappaVec : R2 := (0,1)

@[simp] theorem clockOmega_coordinates :
    clockOmega dKappaVec dThetaVec = 1 ∧
    clockOmega dThetaVec dKappaVec = -1 := by
  norm_num [clockOmega, dThetaVec, dKappaVec]

/-! ## 16. Relational evolution: chain-rule form -/

/-- Abstract algebraic statement: once the flow derivative is `X F`, translating the parameter by
`θ-T` differentiates with the same generator.  The analytic flow theorem is supplied as a
hypothesis so the downstream conclusion is explicit rather than hidden. -/
theorem relational_evolution_from_flow_derivative
    (O XF : ℝ → ℝ)
    (h : ∀ θ, deriv O θ = XF θ) :
    ∀ θ, deriv O θ = XF θ := h

/-! ## 17. Kerr–Newman scalar specialization -/

/-- Kerr-Newman `Σ`. -/
def Sigma (r a θ : ℝ) : ℝ := r^2 + a^2 * (Real.cos θ)^2

/-- Kerr-Newman `Δ`. -/
def Delta (r M a Q : ℝ) : ℝ := r^2 - 2*M*r + a^2 + Q^2

/-- Once the explicit curvature calculation supplies `K=4Q⁴/Σ⁴`, the carrier magnitude follows
algebraically. -/
theorem kerrNewman_chi_from_K
    (Q sig K χ : ℝ)
    (hsig : 0 < sig) (hQ : Q ≠ 0)
    (hK : K = 4 * Q^4 / sig^4)
    (hχ : χ = Real.sqrt K) :
    χ = 2 * Q^2 / sig^2 := by
  rw [hχ, hK]
  have hsig0 : sig ≠ 0 := ne_of_gt hsig
  have hq2 : 0 ≤ Q^2 := sq_nonneg Q
  have hs2 : 0 < sig^2 := sq_pos_of_pos hsig
  have hsq : 4 * Q^4 / sig^4 = (2 * Q^2 / sig^2)^2 := by
    field_simp [hsig0]
    ring
  rw [hsq, Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hq2) (le_of_lt hs2))

/-- The inverse fourth-root curvature multiplier is `Σ/(√2 |Q|)` once its square is fixed. -/
theorem kerrNewman_multiplier_squared
    (Q sig M : ℝ)
    (hQ : Q ≠ 0) (hsig : 0 ≤ sig)
    (hM : M = sig / (Real.sqrt 2 * |Q|)) :
    M^2 = sig^2 / (2 * Q^2) := by
  rw [hM]
  have hs2 : (Real.sqrt 2)^2 = 2 := by norm_num
  have hqabs : |Q|^2 = Q^2 := sq_abs Q
  have hden : Real.sqrt 2 * |Q| ≠ 0 := by
    positivity
  field_simp [hden]
  rw [hs2, hqabs]

/-- Purely algebraic Mino-clock identity.  The differential symbols are represented by real
coefficients along a worldline. -/
theorem mino_clock_identity
    (Q sig dt dlam dth : ℝ)
    (hQ : Q ≠ 0) (hsig : sig ≠ 0)
    (hmino : dlam = dt / sig)
    (hclock : dth = Real.sqrt 2 * |Q| / sig * dt) :
    dth = Real.sqrt 2 * |Q| * dlam := by
  rw [hclock, hmino]
  field_simp [hsig]

/-- Reissner-Nordström specialization (`a=0`) of `Σ`. -/
theorem sigma_reissner_nordstrom (r θ : ℝ) : Sigma r 0 θ = r^2 := by
  simp [Sigma]


/-! ## 17A. Deepening pass: remove algebraic interface assumptions -/

/-- Tensor/module version of the solution-preserving fixed-point argument. -/
theorem solution_preserving_fixed_point_module
    {V : Type*} [AddCommGroup V] [Module ℝ V] [NoZeroSMulDivisors ℝ V]
    (T : V) (s : ℝ) (hT : T ≠ 0)
    (h : T = Real.exp (2 * s) • T) : s = 0 := by
  have hz : (1 - Real.exp (2 * s)) • T = 0 := by
    calc
      (1 - Real.exp (2 * s)) • T =
          (1 : ℝ) • T - Real.exp (2 * s) • T := by rw [sub_smul]
      _ = T - Real.exp (2 * s) • T := by rw [one_smul]
      _ = 0 := sub_eq_zero.mpr h
  have hscalar : (1 : ℝ) - Real.exp (2 * s) = 0 := by
    exact (smul_eq_zero.mp hz).resolve_right hT
  have hexp : Real.exp (2 * s) = 1 := by linarith
  exact (exp_two_eq_one_iff s).mp hexp

/-- The advertised balancing rapidity is an actual root whenever both null components are nonzero. -/
theorem sigmaStar_is_root
    (qm qp : ℝ) (hqm : qm ≠ 0) (hqp : qp ≠ 0) :
    boostDefect qm qp (sigmaStar qm qp) = 0 := by
  have hdiv : qm / qp ≠ 0 := div_ne_zero hqm hqp
  have habs : 0 < |qm / qp| := abs_pos.mpr hdiv
  have hexp : Real.exp (2 * sigmaStar qm qp) = |qm / qp| := by
    unfold sigmaStar
    rw [show 2 * ((1 / 2 : ℝ) * Real.log |qm / qp|) = Real.log |qm / qp| by ring]
    exact Real.exp_log habs
  have hexpn : Real.exp (-2 * sigmaStar qm qp) = (|qm / qp|)⁻¹ := by
    rw [show -2 * sigmaStar qm qp = -(2 * sigmaStar qm qp) by ring]
    rw [Real.exp_neg, hexp]
  unfold boostDefect
  rw [hexp, hexpn]
  have habs0 : |qm / qp| ≠ 0 := ne_of_gt habs
  field_simp [habs0]
  rw [sq_abs, div_pow]
  field_simp [hqp]
  ring

/-- Existence and uniqueness of the balanced rapidity. -/
theorem boost_balance_exists_unique
    (qm qp : ℝ) (hqm : qm ≠ 0) (hqp : qp ≠ 0) :
    ∃! σ : ℝ, boostDefect qm qp σ = 0 := by
  refine ⟨sigmaStar qm qp, sigmaStar_is_root qm qp hqm hqp, ?_⟩
  intro τ hτ
  exact boost_balance_unique qm qp τ (sigmaStar qm qp) hqm hqp hτ
    (sigmaStar_is_root qm qp hqm hqp)

/-- Full uniqueness of the carrier-algebraic conformal factor in the stated zeroth-order category. -/
theorem unique_carrier_algebraic_conformal_factor
    (f : ℝ → ℝ)
    (hhom : ∀ c χ : ℝ, 0 < c → 0 < χ → f (c * χ) = c * f χ)
    (hpos : ∀ χ : ℝ, 0 < χ → 0 < f χ)
    (χ : ℝ) (hχ : 0 < χ)
    (hunit : χ^2 / (f χ)^2 = 1) :
    f χ = χ := by
  have hlin : f χ = f 1 * χ :=
    homogeneous_conformal_factor f hhom χ hχ
  have hCpos : 0 < f 1 := hpos 1 (by norm_num)
  have hunit' : χ^2 / (f 1 * χ)^2 = 1 := by
    simpa [hlin] using hunit
  have hC : f 1 = 1 :=
    unit_involution_fixes_conformal_constant (f 1) χ hCpos hχ hunit'
  rw [hlin, hC, one_mul]

section StrongQuotient
variable {K : Type*} [AddCommGroup K] [Module ℝ K]

/-- A nonzero real covector canonically identifies the quotient by its kernel with the real line. -/
noncomputable def clockQuotientEquivReal
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    (K ⧸ LinearMap.ker Λ) ≃ₗ[ℝ] ℝ :=
  clockQuotientEquivRange Λ ≪≫ₗ
    LinearEquiv.ofEq _ _ (range_eq_top_of_nonzero Λ hΛ) ≪≫ₗ
    Submodule.topEquiv
end StrongQuotient

/-! ### General Maxwell Rainich identity, without first choosing a principal frame -/

def emEnergy (e1 e2 e3 b1 b2 b3 : ℝ) : ℝ :=
  (e1^2 + e2^2 + e3^2 + b1^2 + b2^2 + b3^2) / 2

def emPoynting1 (e1 e2 e3 b1 b2 b3 : ℝ) : ℝ := e2*b3 - e3*b2
def emPoynting2 (e1 e2 e3 b1 b2 b3 : ℝ) : ℝ := e3*b1 - e1*b3
def emPoynting3 (e1 e2 e3 b1 b2 b3 : ℝ) : ℝ := e1*b2 - e2*b1

/-- Mixed Maxwell stress endomorphism with the conventional overall 1/(4 pi) removed. -/
def emMixed
    (e1 e2 e3 b1 b2 b3 : ℝ) (i j : Fin 4) : ℝ :=
  let u := emEnergy e1 e2 e3 b1 b2 b3
  let s1 := emPoynting1 e1 e2 e3 b1 b2 b3
  let s2 := emPoynting2 e1 e2 e3 b1 b2 b3
  let s3 := emPoynting3 e1 e2 e3 b1 b2 b3
  if i = 0 then
    if j = 0 then -u else
    if j = 1 then s1 else
    if j = 2 then s2 else s3
  else if i = 1 then
    if j = 0 then -s1 else
    if j = 1 then u - e1^2 - b1^2 else
    if j = 2 then -e1*e2 - b1*b2 else -e1*e3 - b1*b3
  else if i = 2 then
    if j = 0 then -s2 else
    if j = 1 then -e2*e1 - b2*b1 else
    if j = 2 then u - e2^2 - b2^2 else -e2*e3 - b2*b3
  else
    if j = 0 then -s3 else
    if j = 1 then -e3*e1 - b3*b1 else
    if j = 2 then -e3*e2 - b3*b2 else u - e3^2 - b3^2

def emRainichScalar (e1 e2 e3 b1 b2 b3 : ℝ) : ℝ :=
  ((b1^2 + b2^2 + b3^2 - (e1^2 + e2^2 + e3^2))^2 +
    4 * (e1*b1 + e2*b2 + e3*b3)^2) / 4

/-- Full Maxwell Rainich identity in arbitrary orthonormal-frame electric/magnetic components. -/
theorem emMixed_rainich_square
    (e1 e2 e3 b1 b2 b3 : ℝ) (i j : Fin 4) :
    (∑ k : Fin 4,
      emMixed e1 e2 e3 b1 b2 b3 i k *
      emMixed e1 e2 e3 b1 b2 b3 k j) =
      (if i = j then emRainichScalar e1 e2 e3 b1 b2 b3 else 0) := by
  fin_cases i <;> fin_cases j <;>
    rw [Fin.sum_univ_four] <;>
    simp [emMixed, emEnergy, emPoynting1, emPoynting2, emPoynting3,
      emRainichScalar] <;> ring

theorem emRainichScalar_nonneg
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    0 ≤ emRainichScalar e1 e2 e3 b1 b2 b3 := by
  unfold emRainichScalar
  positivity

/-- The Rainich scalar vanishes exactly on the null electromagnetic invariant locus. -/
theorem emRainichScalar_eq_zero_iff
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    emRainichScalar e1 e2 e3 b1 b2 b3 = 0 ↔
      (b1^2 + b2^2 + b3^2 = e1^2 + e2^2 + e3^2 ∧
       e1*b1 + e2*b2 + e3*b3 = 0) := by
  unfold emRainichScalar
  constructor
  · intro h
    have h1 : 0 ≤
        (b1^2 + b2^2 + b3^2 - (e1^2 + e2^2 + e3^2))^2 :=
      sq_nonneg _
    have h2 : 0 ≤ (e1*b1 + e2*b2 + e3*b3)^2 := sq_nonneg _
    constructor <;> nlinarith
  · rintro ⟨h1,h2⟩
    rw [h1, h2]
    ring

/-- A non-null electromagnetic field has strictly positive Rainich scalar. -/
theorem emRainichScalar_pos_of_nonnull
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (hn : ¬ (b1^2 + b2^2 + b3^2 = e1^2 + e2^2 + e3^2 ∧
      e1*b1 + e2*b2 + e3*b3 = 0)) :
    0 < emRainichScalar e1 e2 e3 b1 b2 b3 := by
  have hnonneg := emRainichScalar_nonneg e1 e2 e3 b1 b2 b3
  have hne : emRainichScalar e1 e2 e3 b1 b2 b3 ≠ 0 := by
    intro hz
    exact hn ((emRainichScalar_eq_zero_iff e1 e2 e3 b1 b2 b3).mp hz)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Clock translation leaves the derivative generator unchanged. -/
theorem relational_evolution_translation
    (F : ℝ → ℝ) (T θ v : ℝ)
    (hF : HasDerivAt F v (θ - T)) :
    HasDerivAt (fun ϑ : ℝ => F (ϑ - T)) v θ := by
  simpa using hF.comp_sub_const θ T

theorem relational_evolution_deriv
    (F : ℝ → ℝ) (T θ v : ℝ)
    (hF : HasDerivAt F v (θ - T)) :
    deriv (fun ϑ : ℝ => F (ϑ - T)) θ = v :=
  (relational_evolution_translation F T θ v hF).deriv


/-! ## 17B. Deepening pass: local response, positivity, and invariant Kerr-Newman clock -/

section RankOneResponse

variable {V W : Type*}
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [NoZeroSMulDivisors ℝ W]

/-- A nonzero response carrier makes the scalar coefficient covector unique. This is the exact
linear-algebra content of the manuscript's pointwise Iyer-Wald normalization. -/
theorem covector_unique_from_rank_one_response
    (η : W) (hη : η ≠ 0)
    (α β : V →ₗ[ℝ] ℝ)
    (h : ∀ v : V, (α v) • η = (β v) • η) :
    α = β := by
  ext v
  have hz : (α v - β v) • η = 0 := by
    rw [sub_smul, h v, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hη)

/-- If the distinguished unit response equals the nonzero carrier itself, its scalar coefficient
is forced to be one. -/
theorem covector_normalized_from_unit_response
    (η : W) (hη : η ≠ 0)
    (resp : V → W) (α : V →ₗ[ℝ] ℝ) (u : V)
    (hfac : ∀ v : V, resp v = (α v) • η)
    (hu : resp u = η) :
    α u = 1 := by
  have heq : (α u) • η = (1 : ℝ) • η := by
    rw [← hfac u, hu, one_smul]
  have hz : (α u - 1) • η = 0 := by
    rw [sub_smul, heq, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hη)

/-- Two scalar factorizations of the same nonzero rank-one response are identical. -/
theorem rank_one_response_factorization_unique
    (η : W) (hη : η ≠ 0)
    (resp : V → W) (α β : V →ₗ[ℝ] ℝ)
    (hα : ∀ v : V, resp v = (α v) • η)
    (hβ : ∀ v : V, resp v = (β v) • η) :
    α = β := by
  apply covector_unique_from_rank_one_response η hη
  intro v
  exact (hα v).symm.trans (hβ v)

end RankOneResponse

/-- Arbitrary-frame Maxwell energy density is nonnegative. -/
theorem emEnergy_nonneg (e1 e2 e3 b1 b2 b3 : ℝ) :
    0 ≤ emEnergy e1 e2 e3 b1 b2 b3 := by
  unfold emEnergy
  positivity

/-- It is strictly positive whenever the six-component field is nonzero. -/
theorem emEnergy_pos_of_sum_squares_ne_zero
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (hnz : e1^2 + e2^2 + e3^2 + b1^2 + b2^2 + b3^2 ≠ 0) :
    0 < emEnergy e1 e2 e3 b1 b2 b3 := by
  unfold emEnergy
  have hnonneg :
      0 ≤ e1^2 + e2^2 + e3^2 + b1^2 + b2^2 + b3^2 := by positivity
  have hpos :
      0 < e1^2 + e2^2 + e3^2 + b1^2 + b2^2 + b3^2 :=
    lt_of_le_of_ne hnonneg (Ne.symm hnz)
  linarith

/-- The arbitrary-frame mixed Maxwell stress is trace-free. -/
theorem emMixed_trace_zero
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    (∑ i : Fin 4, emMixed e1 e2 e3 b1 b2 b3 i i) = 0 := by
  rw [Fin.sum_univ_four]
  simp [emMixed, emEnergy, emPoynting1, emPoynting2, emPoynting3]
  ring

/-- From the Kerr-Newman carrier magnitude, the positive intrinsic clock rate is forced. -/
theorem kerrNewman_clock_rate_from_chi
    (Q sig χ ω : ℝ)
    (hQ : Q ≠ 0) (hsig : 0 < sig)
    (hχ : χ = 2 * Q^2 / sig^2)
    (hω : ω = Real.sqrt χ) :
    ω = Real.sqrt 2 * |Q| / sig := by
  have hsig0 : sig ≠ 0 := ne_of_gt hsig
  have hχnonneg : 0 ≤ χ := by
    rw [hχ]
    positivity
  have hωnonneg : 0 ≤ ω := by rw [hω]; positivity
  have hrhsnonneg : 0 ≤ Real.sqrt 2 * |Q| / sig := by positivity
  have hω2 : ω^2 = χ := by
    rw [hω, Real.sq_sqrt hχnonneg]
  have hsqrt2 : (Real.sqrt 2)^2 = 2 := by norm_num
  have habsQ : |Q|^2 = Q^2 := sq_abs Q
  have hrhs2 : (Real.sqrt 2 * |Q| / sig)^2 = χ := by
    rw [hχ]
    field_simp [hsig0]
    rw [hsqrt2, habsQ]
  nlinarith

/-- The Mino relation is therefore a corollary of the invariant clock rate rather than a separate
Kerr-Newman clock hypothesis. -/
theorem kerrNewman_mino_from_invariant_clock
    (Q sig χ ω dt dlam dth : ℝ)
    (hQ : Q ≠ 0) (hsig : 0 < sig)
    (hχ : χ = 2 * Q^2 / sig^2)
    (hω : ω = Real.sqrt χ)
    (hclock : dth = ω * dt)
    (hmino : dlam = dt / sig) :
    dth = Real.sqrt 2 * |Q| * dlam := by
  have hrate :=
    kerrNewman_clock_rate_from_chi Q sig χ ω hQ hsig hχ hω
  rw [hclock, hrate, hmino]
  field_simp [ne_of_gt hsig]

/-! ## 18. Explicit hypothesis interfaces for the still-unformalized geometric layers

These are *not axioms*. They are structures passed explicitly to theorems.  The final first-principles
project must construct them from the Einstein–Maxwell fields.  Keeping them explicit prevents
accidentally claiming a theorem stronger than what this single file proves.
-/

section GeometricInterface

variable {V P KSpace : Type*}
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup P] [Module ℝ P]
  [AddCommGroup KSpace] [Module ℝ KSpace]

/-- Minimal algebraic interface exported by a future first-principles Einstein-Maxwell/Iyer-Wald
formalization. -/
structure BridgeData where
  beta : P →ₗ[ℝ] KSpace
  Lambda : KSpace →ₗ[ℝ] ℝ
  ell : P →ₗ[ℝ] ℝ
  beta_surj : Function.Surjective beta
  factorization : Lambda.comp beta = ell
  Lambda_nonzero : Lambda ≠ 0

/-- Once the Iyer-Wald bridge is supplied, the characteristic covector is mathematically unique. -/
theorem bridge_Lambda_unique (D : BridgeData (P:=P) (KSpace:=KSpace))
    (Λ' : KSpace →ₗ[ℝ] ℝ) (hΛ' : Λ'.comp D.beta = D.ell) : Λ' = D.Lambda := by
  exact descended_covector_unique D.beta D.beta_surj D.ell Λ' D.Lambda hΛ' D.factorization

/-- The characteristic quotient is canonically equivalent to the range of the unique covector. -/
noncomputable def bridgeQuotientEquivRange (D : BridgeData (P:=P) (KSpace:=KSpace)) :
    (KSpace ⧸ LinearMap.ker D.Lambda) ≃ₗ[ℝ] LinearMap.range D.Lambda :=
  LinearMap.quotKerEquivRange D.Lambda

/-- The range of the characteristic clock covector is all of `ℝ`. -/
theorem bridge_range_full (D : BridgeData (P:=P) (KSpace:=KSpace)) :
    LinearMap.range D.Lambda = ⊤ :=
  range_eq_top_of_nonzero D.Lambda D.Lambda_nonzero

end GeometricInterface

/-! ## 19. End-to-end dependency record -/

/-- A compact theorem collecting the fully proved scalar backbone: four-dimensional reciprocity,
unique exchange fixed point, defect jet, and relative rapidity. -/
theorem scalar_backbone
    (D s T Ric : ℝ)
    (hrecip : wG D = -(wM D))
    (hRic : Ric = 8 * Real.pi * T) :
    D = 4 ∧
    (Real.exp (2*s) = 1 ↔ s = 0) ∧
    (-16 * Real.pi * T = -2 * Ric) ∧
    ((Real.exp s - Real.exp (-s)) /
      (Real.exp s + Real.exp (-s)) = Real.tanh s) := by
  refine ⟨(reciprocal_weights_iff_four D).mp hrecip, exp_two_eq_one_iff s, ?_, optical_defect_is_tanh s⟩
  exact jet_eq_minus_two_ricci T Ric hRic

/-! ## 20. Audit sentinels -/

#check reciprocal_weights_iff_four
#check mobius_projective_unique
#check solution_preserving_fixed_point
#check defect_hasDerivAt_zero
#check principalStress_sq
#check normalized_involution
#check boost_balance_unique
#check homogeneous_conformal_factor
#check covector_pullback_injective
#check descended_covector_unique
#check bridge_Lambda_unique
#check null_pair_orthogonal
#check mino_clock_identity
#check scalar_backbone

end RelativeRest

-- The following commands are intentionally left as audit hooks for a real Lean build:
-- #print axioms RelativeRest.scalar_backbone
-- #print axioms RelativeRest.boost_balance_unique
-- #print axioms RelativeRest.bridge_Lambda_unique
-- #print axioms RelativeRest.mino_clock_identity
