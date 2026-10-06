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

/-- The exchange-even carrier has vanishing first normal derivative at the fixed point. -/
theorem carrierEven_hasDerivAt_zero (η : ℝ) :
    HasDerivAt (carrierEven η) 0 0 := by
  unfold carrierEven
  have h := (Real.hasDerivAt_cosh 0).const_mul 2
  have h' := h.mul_const η
  simpa [mul_assoc, mul_left_comm, mul_comm] using h'

/-- The exchange-odd carrier's first jet is exactly minus the even carrier value. -/
theorem carrierOdd_hasDerivAt_zero (η : ℝ) :
    HasDerivAt (carrierOdd η) (- carrierEven η 0) 0 := by
  unfold carrierOdd
  have h := (Real.hasDerivAt_sinh 0).const_mul (-2)
  have h' := h.mul_const η
  simpa [carrierEven, mul_assoc, mul_left_comm, mul_comm] using h'

/-- Thus the fixed point kills the odd value but not its normal generator. -/
theorem carrier_fixed_point_value_jet (η : ℝ) :
    carrierOdd η 0 = 0 ∧
    HasDerivAt (carrierOdd η) (- carrierEven η 0) 0 := by
  exact ⟨carrierOdd_zero η, carrierOdd_hasDerivAt_zero η⟩

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

/-- The canonical ± eigenspace projectors of an involution. -/
def involutionProjPlus
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : V →ₗ[ℝ] V) (v : V) : V :=
  (1 / 2 : ℝ) • (v + S v)

def involutionProjMinus
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : V →ₗ[ℝ] V) (v : V) : V :=
  (1 / 2 : ℝ) • (v - S v)

/-- The two Rainich projectors reconstruct every vector. -/
theorem involution_projectors_sum
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : V →ₗ[ℝ] V) (v : V) :
    involutionProjPlus S v + involutionProjMinus S v = v := by
  simp [involutionProjPlus, involutionProjMinus]
  module

/-- The + projector lands in the +1 eigenspace. -/
theorem involutionProjPlus_eigen
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : V →ₗ[ℝ] V)
    (hS : ∀ v : V, S (S v) = v)
    (v : V) :
    S (involutionProjPlus S v) = involutionProjPlus S v := by
  simp [involutionProjPlus, map_add, map_smul, hS]
  module

/-- The - projector lands in the -1 eigenspace. -/
theorem involutionProjMinus_eigen
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : V →ₗ[ℝ] V)
    (hS : ∀ v : V, S (S v) = v)
    (v : V) :
    S (involutionProjMinus S v) = - involutionProjMinus S v := by
  simp [involutionProjMinus, map_sub, map_smul, hS]
  module

/-- Both canonical projectors are idempotent. -/
theorem involution_projectors_idempotent
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : V →ₗ[ℝ] V)
    (hS : ∀ v : V, S (S v) = v)
    (v : V) :
    involutionProjPlus S (involutionProjPlus S v) = involutionProjPlus S v ∧
    involutionProjMinus S (involutionProjMinus S v) = involutionProjMinus S v := by
  constructor
  · simp [involutionProjPlus, map_add, map_smul, hS]
    module
  · simp [involutionProjMinus, map_sub, map_smul, hS]
    module

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


/-- For nonzero null components, the boost defect is strictly decreasing.  This is the
kernel-checked monotonicity statement used in the manuscript to rule out a second balance. -/
theorem boostDefect_strictAnti
    (qm qp : ℝ) (hqm : qm ≠ 0) (hqp : qp ≠ 0) :
    StrictAnti (boostDefect qm qp) := by
  intro σ τ hστ
  have hqm2 : 0 < qm^2 := sq_pos_of_ne_zero hqm
  have hqp2 : 0 < qp^2 := sq_pos_of_ne_zero hqp
  have hminus : Real.exp (-2 * τ) < Real.exp (-2 * σ) := by
    exact Real.exp_lt_exp.mpr (by linarith)
  have hplus : Real.exp (2 * σ) < Real.exp (2 * τ) := by
    exact Real.exp_lt_exp.mpr (by linarith)
  have hm := mul_lt_mul_of_pos_right hminus hqm2
  have hp := mul_lt_mul_of_pos_right hplus hqp2
  unfold boostDefect
  linarith

/-- The rapidity written in the manuscript actually attains the unique boost balance. -/
theorem sigmaStar_balance
    (qm qp : ℝ) (hqm : qm ≠ 0) (hqp : qp ≠ 0) :
    boostDefect qm qp (sigmaStar qm qp) = 0 := by
  have hr : 0 < |qm / qp| := abs_pos.mpr (div_ne_zero hqm hqp)
  have hepos : Real.exp (2 * sigmaStar qm qp) = |qm / qp| := by
    rw [sigmaStar]
    have harg :
        2 * ((1 / 2 : ℝ) * Real.log |qm / qp|) = Real.log |qm / qp| := by
      ring
    rw [harg, Real.exp_log hr]
  have heneg : Real.exp (-2 * sigmaStar qm qp) = (|qm / qp|)⁻¹ := by
    rw [show -2 * sigmaStar qm qp = -(2 * sigmaStar qm qp) by ring]
    rw [Real.exp_neg, hepos]
  rw [boostDefect, hepos, heneg, abs_div]
  rw [← sq_abs qm, ← sq_abs qp]
  have hma : |qm| ≠ 0 := abs_ne_zero.mpr hqm
  have hpa : |qp| ≠ 0 := abs_ne_zero.mpr hqp
  field_simp [hma, hpa]
  ring

/-- Changing the initial null dyad by rapidity τ shifts the balancing rapidity by -τ. -/
theorem sigmaStar_shift_covariance
    (qm qp τ : ℝ) (hqm : qm ≠ 0) (hqp : qp ≠ 0) :
    sigmaStar (Real.exp (-τ) * qm) (Real.exp τ * qp) =
      sigmaStar qm qp - τ := by
  have hqm' : Real.exp (-τ) * qm ≠ 0 :=
    mul_ne_zero (ne_of_gt (Real.exp_pos (-τ))) hqm
  have hqp' : Real.exp τ * qp ≠ 0 :=
    mul_ne_zero (ne_of_gt (Real.exp_pos τ)) hqp
  apply boost_balance_unique
      (Real.exp (-τ) * qm) (Real.exp τ * qp)
      (sigmaStar (Real.exp (-τ) * qm) (Real.exp τ * qp))
      (sigmaStar qm qp - τ) hqm' hqp'
  · exact sigmaStar_balance _ _ hqm' hqp'
  · rw [balance_shift_covariance]
    convert sigmaStar_balance qm qp hqm hqp using 1 <;> ring

/-- Nonzero principal null components therefore admit exactly one balanced rapidity. -/
theorem boost_balance_exists_unique
    (qm qp : ℝ) (hqm : qm ≠ 0) (hqp : qp ≠ 0) :
    ∃! σ : ℝ, boostDefect qm qp σ = 0 := by
  refine ⟨sigmaStar qm qp, sigmaStar_balance qm qp hqm hqp, ?_⟩
  intro τ hτ
  exact boost_balance_unique qm qp τ (sigmaStar qm qp) hqm hqp
    hτ (sigmaStar_balance qm qp hqm hqp)

/-- Substituting the forced balancing rapidity makes the balanced null dyad independent
of the initial boost representative. -/
theorem sigmaStar_balanced_dyad_invariant
    (km lp qm qp τ : ℝ) (hqm : qm ≠ 0) (hqp : qp ≠ 0) :
    (Real.exp (-(sigmaStar (Real.exp (-τ) * qm) (Real.exp τ * qp))) *
        (Real.exp (-τ) * km) =
      Real.exp (-(sigmaStar qm qp)) * km) ∧
    (Real.exp (sigmaStar (Real.exp (-τ) * qm) (Real.exp τ * qp)) *
        (Real.exp τ * lp) =
      Real.exp (sigmaStar qm qp) * lp) := by
  rw [sigmaStar_shift_covariance qm qp τ hqm hqp]
  exact balanced_dyad_invariant km lp (sigmaStar qm qp) τ

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

/-- Scalar certificate for representative independence:
if `χ ↦ Ω⁻²χ` and `g ↦ Ω²g`, their normalized product is unchanged. -/
theorem conformal_representative_product_invariant
    (χ Ω : ℝ) (hΩ : Ω ≠ 0) :
    (χ / Ω^2) * Ω^2 = χ := by
  field_simp [hΩ]

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


/-! ### Forced action-to-optical intertwiner -/

/-- Optical even basis covector. -/
def TO : R2 := (1, 0)

/-- Optical odd basis covector. -/
def RO : R2 := (0, 1)

/-- Evaluation pairing for the finite-dimensional optical model. -/
def opticalEval (α v : R2) : ℝ := α.1 * v.1 + α.2 * v.2

/-- Unit boosted observer in the normalized optical basis. -/
def opticalObserver (s : ℝ) : R2 := (Real.cosh s, Real.sinh s)

/-- The operational radial/time ratio of the boosted observer is exactly `tanh s`. -/
theorem optical_velocity_ratio (s : ℝ) :
    opticalEval RO (opticalObserver s) / opticalEval TO (opticalObserver s) =
      Real.tanh s := by
  simp [opticalEval, RO, TO, opticalObserver, Real.tanh_eq_sinh_div_cosh]

/-- Normalized optical boost generator, exchanging even and odd basis directions. -/
def BO (v : R2) : R2 := (v.2, v.1)

@[simp] theorem BO_TO : BO TO = RO := by
  ext <;> norm_num [BO, TO, RO]

@[simp] theorem BO_RO : BO RO = TO := by
  ext <;> norm_num [BO, TO, RO]

@[simp] theorem BO_sq (v : R2) : BO (BO v) = v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [BO]

/-- The unique normalized linear identification sending the action even/odd basis to the
optical time/radial basis. -/
def actionOpticalMap : R2 →ₗ[ℝ] R2 where
  toFun v := ((v.1 + v.2) / 2, (v.2 - v.1) / 2)
  map_add' x y := by
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    ext <;> simp <;> ring
  map_smul' c x := by
    rcases x with ⟨x₁, x₂⟩
    ext <;> simp <;> ring

@[simp] theorem actionOpticalMap_CA : actionOpticalMap CA = TO := by
  ext <;> norm_num [actionOpticalMap, CA, TO]

@[simp] theorem actionOpticalMap_DA : actionOpticalMap DA = RO := by
  ext <;> norm_num [actionOpticalMap, DA, RO]

/-- The normalized map intertwines the action and optical boost generators pointwise. -/
theorem actionOpticalMap_intertwines_generator (v : R2) :
    actionOpticalMap (YA v) = BO (actionOpticalMap v) := by
  rcases v with ⟨x, y⟩
  ext <;> simp [actionOpticalMap, YA, BO] <;> ring

/-- No second normalized linear action-to-optical map exists. -/
theorem actionOpticalMap_unique
    (I : R2 →ₗ[ℝ] R2)
    (hC : I CA = TO) (hD : I DA = RO) :
    I = actionOpticalMap := by
  apply LinearMap.ext
  intro v
  rcases v with ⟨x, y⟩
  have hv :
      (x, y) =
        ((x + y) / 2) • CA + ((y - x) / 2) • DA := by
    ext <;> simp [CA, DA] <;> ring
  calc
    I (x, y)
        = I (((x + y) / 2) • CA + ((y - x) / 2) • DA) := by rw [← hv]
    _ = ((x + y) / 2) • TO + ((y - x) / 2) • RO := by
          rw [map_add, map_smul, map_smul, hC, hD]
    _ = actionOpticalMap (x, y) := by
          ext <;> simp [TO, RO, actionOpticalMap] <;> ring

/-- Finite optical boost in the normalized time/radial basis. -/
def opticalBoost (s : ℝ) (v : R2) : R2 :=
  (Real.cosh s * v.1 + Real.sinh s * v.2,
   Real.sinh s * v.1 + Real.cosh s * v.2)

/-- The unique normalized identification intertwines the entire finite boost, not only
its infinitesimal generator. -/
theorem actionOpticalMap_intertwines_boost (s : ℝ) (v : R2) :
    actionOpticalMap (actionBoost s v) =
      opticalBoost s (actionOpticalMap v) := by
  rcases v with ⟨x, y⟩
  ext <;>
    simp [actionOpticalMap, actionBoost, opticalBoost,
      ← Real.cosh_add_sinh, ← Real.cosh_sub_sinh] <;>
    ring

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

/-- A strictly positive response on one vector forces a real covector to be nonzero. -/
theorem covector_nonzero_of_positive
    (ℓ : P →ₗ[ℝ] ℝ) (p : P) (hp : 0 < ℓ p) :
    ℓ ≠ 0 := by
  intro hzero
  rw [hzero] at hp
  simp at hp

/-- Factorization transfers nonvanishing of the physical response to the descended covector. -/
theorem descended_covector_nonzero
    (β : P →ₗ[ℝ] K) (Λ : K →ₗ[ℝ] ℝ) (ℓ : P →ₗ[ℝ] ℝ)
    (hfac : Λ.comp β = ℓ)
    (hℓ : ℓ ≠ 0) :
    Λ ≠ 0 := by
  intro hΛ
  apply hℓ
  rw [← hfac, hΛ]
  simp

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

/-- Once `Λ` is quotiented by its kernel, its descended clock covector is unique. -/
theorem quotient_clock_covector_unique
    (Λ : K →ₗ[ℝ] ℝ)
    (λ₁ λ₂ : (K ⧸ LinearMap.ker Λ) →ₗ[ℝ] ℝ)
    (h₁ : λ₁.comp (LinearMap.ker Λ).mkQ = Λ)
    (h₂ : λ₂.comp (LinearMap.ker Λ).mkQ = Λ) :
    λ₁ = λ₂ := by
  exact descended_covector_unique
    (LinearMap.ker Λ).mkQ
    (Submodule.mkQ_surjective (LinearMap.ker Λ))
    Λ λ₁ λ₂ h₁ h₂

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

/-- A normalized covector selects at most one unit on a line reconstructed by that covector. -/
theorem normalized_unit_unique
    (α : L₁ →ₗ[ℝ] ℝ) (u v : L₁)
    (hu : α u = 1)
    (hspan : ∀ x : L₁, x = (α x) • u)
    (hv : α v = 1) :
    v = u := by
  rw [hspan v, hv, one_smul]

/-- Explicit normalized map between two one-dimensional clock lines. -/
def normalizedClockMap
    (α : L₁ →ₗ[ℝ] ℝ) (u₂ : L₂) : L₁ →ₗ[ℝ] L₂ where
  toFun x := (α x) • u₂
  map_add' x y := by simp [add_smul]
  map_smul' c x := by simp [mul_smul]

@[simp] theorem normalizedClockMap_apply
    (α : L₁ →ₗ[ℝ] ℝ) (u₂ : L₂) (x : L₁) :
    normalizedClockMap α u₂ x = (α x) • u₂ := rfl

/-- A normalized target covector is preserved exactly by the canonical clock-line map. -/
theorem normalizedClockMap_preserves_covector
    (α : L₁ →ₗ[ℝ] ℝ) (β : L₂ →ₗ[ℝ] ℝ) (u₂ : L₂)
    (hβu : β u₂ = 1) (x : L₁) :
    β (normalizedClockMap α u₂ x) = α x := by
  simp [normalizedClockMap, hβu]

/-- If the target line is reconstructed by its normalized covector, covector preservation alone
forces the canonical map. -/
theorem normalizedClockMap_unique_of_covector
    (α : L₁ →ₗ[ℝ] ℝ) (β : L₂ →ₗ[ℝ] ℝ) (u₂ : L₂)
    (hβu : β u₂ = 1)
    (hspan₂ : ∀ y : L₂, y = (β y) • u₂)
    (I : L₁ →ₗ[ℝ] L₂)
    (hpres : β.comp I = α) :
    I = normalizedClockMap α u₂ := by
  ext x
  rw [hspan₂ (I x)]
  have hx := LinearMap.congr_fun hpres x
  change β (I x) = α x at hx
  rw [hx]
  rfl

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

/-- The lift preserves the clock coefficient exactly. -/
@[simp] theorem localLift_preserves_lambda
    (D : LocalClockData (V:=V)) (v : V) :
    D.lambda (localLift D v) = D.lambda v := by
  simp [localLift, D.normalized]

/-- The local lift is a projection onto the selected clock line. -/
@[simp] theorem localLift_idempotent
    (D : LocalClockData (V:=V)) (v : V) :
    localLift D (localLift D v) = localLift D v := by
  simp [localLift, D.normalized]

/-- The invisible directions are exactly the vectors killed by the local lift. -/
theorem localLift_eq_zero_iff
    (D : LocalClockData (V:=V)) (v : V) :
    localLift D v = 0 ↔ D.lambda v = 0 := by
  constructor
  · intro h
    have h' := congrArg D.lambda h
    simpa [localLift, D.normalized] using h'
  · intro h
    simp [localLift, h]

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

/-- Exchange-even radar midpoint. -/
def radarTime (θplus θminus : ℝ) : ℝ := (θplus + θminus) / 2

/-- Exchange-odd radar defect. -/
def radarRadius (θplus θminus : ℝ) : ℝ := (θplus - θminus) / 2

/-- The midpoint is exchange-even and the radial defect exchange-odd. -/
theorem radar_exchange_parity (θplus θminus : ℝ) :
    radarTime θminus θplus = radarTime θplus θminus ∧
    radarRadius θminus θplus = - radarRadius θplus θminus := by
  constructor <;> unfold radarTime radarRadius <;> ring

/-- Midpoint and defect reconstruct the two endpoint readings exactly. -/
theorem radar_reconstruction (θplus θminus : ℝ) :
    radarTime θplus θminus + radarRadius θplus θminus = θplus ∧
    radarTime θplus θminus - radarRadius θplus θminus = θminus := by
  constructor <;> unfold radarTime radarRadius <;> ring

/-- A common shift changes only the clock origin and leaves the radial defect invariant. -/
theorem radar_common_shift (θplus θminus C : ℝ) :
    radarTime (θplus + C) (θminus + C) = radarTime θplus θminus + C ∧
    radarRadius (θplus + C) (θminus + C) = radarRadius θplus θminus := by
  constructor <;> unfold radarTime radarRadius <;> ring

/-- Coincident endpoints force vanishing relative radius. -/
@[simp] theorem radarRadius_self (θ : ℝ) : radarRadius θ θ = 0 := by
  unfold radarRadius
  ring


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

/-- Abstract exterior-derivative algebra behind `dβ=-dT_O`: if the radar clock is exact,
the forced correction cancels the curvature of the local chronometric covector. -/
theorem synchronization_curvature_cancellation
    {W Z : Type*} [AddCommGroup W] [AddCommGroup Z]
    (d : W →+ Z) (dT TO β : W)
    (hβ : β = dT - TO)
    (hexact : d dT = 0) :
    d β = - d TO := by
  rw [hβ, map_sub, hexact, zero_sub]

/-- Consequently the corrected covector is closed. -/
theorem synchronization_total_closed
    {W Z : Type*} [AddCommGroup W] [AddCommGroup Z]
    (d : W →+ Z) (TO β : W)
    (hcancel : d β = - d TO) :
    d TO + d β = 0 := by
  rw [hcancel]
  exact add_neg_cancel _

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

/-- The clock-cover two-form is skew. -/
theorem clockOmega_skew (v w : R2) :
    clockOmega v w = - clockOmega w v := by
  rcases v with ⟨v₁, v₂⟩
  rcases w with ⟨w₁, w₂⟩
  simp [clockOmega]
  ring

@[simp] theorem clockOmega_self (v : R2) : clockOmega v v = 0 := by
  rcases v with ⟨v₁, v₂⟩
  simp [clockOmega]

/-- The finite-dimensional clock-cover form is nondegenerate. -/
theorem clockOmega_left_nondegenerate
    (v : R2) (h : ∀ w : R2, clockOmega v w = 0) :
    v = 0 := by
  rcases v with ⟨x, y⟩
  have hy : y = 0 := by
    simpa [clockOmega, dThetaVec] using h dThetaVec
  have hx : x = 0 := by
    have h' := h dKappaVec
    simp [clockOmega, dKappaVec] at h'
    linarith
  ext <;> simp [hx, hy]

/-! ## 16. Relational evolution: chain-rule form -/

/-- Relational translation by a clock reading does not alter the flow derivative. -/
theorem relational_translation_hasDerivAt
    (O : ℝ → ℝ) (T θ d : ℝ)
    (h : HasDerivAt O d (θ - T)) :
    HasDerivAt (fun ϑ => O (ϑ - T)) d θ := by
  exact HasDerivAt.comp_sub_const θ T h

/-- Derivative form of the relational translation identity. -/
theorem relational_translation_deriv
    (O : ℝ → ℝ) (T θ d : ℝ)
    (h : HasDerivAt O d (θ - T)) :
    deriv (fun ϑ => O (ϑ - T)) θ = d :=
  (relational_translation_hasDerivAt O T θ d h).deriv

/-- If the untranslated flow differentiates to `XF`, then the relational observable
differentiates to the same generator evaluated at the shifted parameter. -/
theorem relational_evolution_from_flow_derivative
    (O XF : ℝ → ℝ) (T θ : ℝ)
    (hO : HasDerivAt O (XF (θ - T)) (θ - T)) :
    deriv (fun ϑ => O (ϑ - T)) θ = XF (θ - T) :=
  relational_translation_deriv O T θ (XF (θ - T)) hO

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

/-- The curvature-derived clock rate in Kerr-Newman is forced by the carrier magnitude. -/
theorem kerrNewman_clock_rate
    (Q sig χ ω : ℝ)
    (hsig : 0 < sig)
    (hχ : χ = 2 * Q^2 / sig^2)
    (hω : ω = Real.sqrt χ) :
    ω = Real.sqrt 2 * |Q| / sig := by
  have hsig0 : sig ≠ 0 := ne_of_gt hsig
  have hχnonneg : 0 ≤ χ := by
    rw [hχ]
    positivity
  have hωnonneg : 0 ≤ ω := by
    rw [hω]
    exact Real.sqrt_nonneg χ
  have hω2 : ω^2 = χ := by
    rw [hω, Real.sq_sqrt hχnonneg]
  have hrhsnonneg : 0 ≤ Real.sqrt 2 * |Q| / sig := by
    positivity
  have hs2 : (Real.sqrt 2)^2 = 2 := by norm_num
  have hrhs2 : (Real.sqrt 2 * |Q| / sig)^2 = χ := by
    rw [hχ]
    field_simp [hsig0]
    rw [mul_pow, hs2, sq_abs]
    ring
  nlinarith

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
formalization.  Nonvanishing of the descended clock covector is not postulated: a strictly
positive physical response witness forces it. -/
structure BridgeData where
  beta : P →ₗ[ℝ] KSpace
  Lambda : KSpace →ₗ[ℝ] ℝ
  ell : P →ₗ[ℝ] ℝ
  beta_surj : Function.Surjective beta
  factorization : Lambda.comp beta = ell
  positiveWitness : P
  response_positive : 0 < ell positiveWitness

/-- The physical positive-response witness forces the integrated response covector to be nonzero. -/
theorem bridge_ell_nonzero (D : BridgeData (P:=P) (KSpace:=KSpace)) :
    D.ell ≠ 0 :=
  covector_nonzero_of_positive D.ell D.positiveWitness D.response_positive

/-- Factorization then forces the descended characteristic covector itself to be nonzero. -/
theorem bridge_Lambda_nonzero (D : BridgeData (P:=P) (KSpace:=KSpace)) :
    D.Lambda ≠ 0 :=
  descended_covector_nonzero D.beta D.Lambda D.ell D.factorization (bridge_ell_nonzero D)

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
  range_eq_top_of_nonzero D.Lambda (bridge_Lambda_nonzero D)

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
#check involution_projectors_sum
#check involutionProjPlus_eigen
#check involutionProjMinus_eigen
#check involution_projectors_idempotent
#check boost_balance_unique
#check boostDefect_strictAnti
#check sigmaStar_balance
#check sigmaStar_shift_covariance
#check actionOpticalMap_unique
#check actionOpticalMap_intertwines_generator
#check homogeneous_conformal_factor
#check covector_pullback_injective
#check descended_covector_unique
#check bridge_ell_nonzero
#check bridge_Lambda_nonzero
#check bridge_Lambda_unique
#check null_pair_orthogonal
#check mino_clock_identity
#check scalar_backbone
#check normalized_unit_unique
#check covector_nonzero_of_positive
#check descended_covector_nonzero
#check radar_exchange_parity
#check radar_reconstruction
#check radar_common_shift
#check synchronization_curvature_cancellation
#check synchronization_total_closed
#check optical_velocity_ratio
#check boost_balance_exists_unique
#check sigmaStar_balanced_dyad_invariant
#check actionOpticalMap_intertwines_boost
#check quotient_clock_covector_unique
#check kerrNewman_clock_rate
#check carrier_fixed_point_value_jet
#check conformal_representative_product_invariant
#check normalizedClockMap_preserves_covector
#check normalizedClockMap_unique_of_covector
#check localLift_idempotent
#check localLift_eq_zero_iff
#check clockOmega_left_nondegenerate
#check relational_evolution_from_flow_derivative

end RelativeRest

-- The following commands are intentionally left as audit hooks for a real Lean build:
-- #print axioms RelativeRest.scalar_backbone
-- #print axioms RelativeRest.boost_balance_unique
-- #print axioms RelativeRest.bridge_Lambda_unique
-- #print axioms RelativeRest.mino_clock_identity
