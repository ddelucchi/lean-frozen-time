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

/-- On the positive projective sector, relative rest is the unique zero of the defect coordinate. -/
theorem delta_eq_zero_iff_one (r : ℝ) (hr : 0 < r) :
    delta r = 0 ↔ r = 1 := by
  have hden : r + 1 ≠ 0 := by positivity
  constructor
  · intro h
    have hn : r - 1 = 0 := by
      rcases (div_eq_zero_iff.mp (by simpa [delta] using h)) with hn | hd
      · exact hn
      · exact False.elim (hden hd)
    linarith
  · rintro rfl
    exact delta_one

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


/-! ### Primitive homothety count behind the action weights -/

/-- Volume density weight under `g ↦ ρ²g`. -/
def volumeHomothetyExponent (D : ℝ) : ℝ := D

/-- Scalar-curvature weight under a constant homothety. -/
def scalarCurvatureHomothetyExponent : ℝ := -2

/-- Each inverse metric contributes `ρ⁻²`; Maxwell `F²` contains two inverse metrics. -/
def maxwellInverseMetricExponent : ℝ := -4

/-- The quadratic Maxwell density carries two powers of the potential/field scaling `λ`. -/
def maxwellFieldAmplitudeExponent : ℝ := 2

/-- The Einstein-Hilbert density weight `D-2` is exactly volume plus scalar-curvature weight. -/
theorem gravScaleExponent_from_primitive_weights (D : ℝ) :
    gravScaleExponent D =
      volumeHomothetyExponent D + scalarCurvatureHomothetyExponent := by
  simp [gravScaleExponent, volumeHomothetyExponent,
    scalarCurvatureHomothetyExponent]
  ring

/-- The Maxwell metric weight `D-4` is exactly volume plus the two inverse-metric weights. -/
theorem maxwellMetricScaleExponent_from_primitive_weights (D : ℝ) :
    maxwellMetricScaleExponent D =
      volumeHomothetyExponent D + maxwellInverseMetricExponent := by
  simp [maxwellMetricScaleExponent, volumeHomothetyExponent,
    maxwellInverseMetricExponent]
  ring

/-- After `ρ=e^{(u-s)/2}`, the gravity relative exponent is forced by the primitive weights. -/
theorem gravity_relative_weight_from_primitive_counts (D : ℝ) :
    (volumeHomothetyExponent D + scalarCurvatureHomothetyExponent) *
        (-1 / 2 : ℝ) =
      wG D := by
  simp [volumeHomothetyExponent, scalarCurvatureHomothetyExponent, wG]
  ring

/-- After `ρ=e^{(u-s)/2}`, `λ=e^{(u+s)/2}`, the Maxwell relative exponent is
forced by metric and field-amplitude counts. -/
theorem maxwell_relative_weight_from_primitive_counts (D : ℝ) :
    (volumeHomothetyExponent D + maxwellInverseMetricExponent) *
          (-1 / 2 : ℝ) +
        maxwellFieldAmplitudeExponent * (1 / 2 : ℝ) =
      wM D := by
  simp [volumeHomothetyExponent, maxwellInverseMetricExponent,
    maxwellFieldAmplitudeExponent, wM]
  ring

/-- Thus primitive homothety counting itself yields reciprocal relative action weights
if and only if `D=4`. -/
theorem primitive_relative_weights_reciprocal_iff_four (D : ℝ) :
    (volumeHomothetyExponent D + scalarCurvatureHomothetyExponent) *
        (-1 / 2 : ℝ) =
      -((volumeHomothetyExponent D + maxwellInverseMetricExponent) *
          (-1 / 2 : ℝ) +
        maxwellFieldAmplitudeExponent * (1 / 2 : ℝ)) ↔
      D = 4 := by
  rw [gravity_relative_weight_from_primitive_counts,
    maxwell_relative_weight_from_primitive_counts]
  exact reciprocal_weights_iff_four D


/-- Conformal weight of the Hodge star on a p-form under `g ↦ Ω²g`. -/
def hodgeConformalExponent (D p : ℝ) : ℝ := D - 2 * p

/-- Two-forms have conformally invariant Hodge dual exactly in four dimensions. -/
theorem hodge_twoform_conformal_iff_four (D : ℝ) :
    hodgeConformalExponent D 2 = 0 ↔ D = 4 := by
  unfold hodgeConformalExponent
  constructor <;> intro h <;> linarith

@[simp] theorem hodge_twoform_four_dimensional :
    hodgeConformalExponent 4 2 = 0 := by
  norm_num [hodgeConformalExponent]

/-- The Maxwell action's constant-homothety exponent is the same four-dimensional
exceptional exponent as the Hodge star on two-forms. -/
theorem maxwell_hodge_exponents_agree (D : ℝ) :
    maxwellMetricScaleExponent D = hodgeConformalExponent D 2 := by
  unfold maxwellMetricScaleExponent hodgeConformalExponent
  ring

/-- Substitution `ρ=e^((u-s)/2)`, `λ=e^((u+s)/2)` gives the advertised relative exponents. -/
theorem relative_exponent_algebra (D : ℝ) :
    (-(D - 2) / 2 = wG D) ∧ ((D - 4) * (-1 / 2) + 2 * (1 / 2) = wM D) := by
  constructor
  · rfl
  · unfold wM
    ring

/-- Positive common/relative parametrization used in the manuscript. -/
def rhoUS (u s : ℝ) : ℝ := Real.exp ((u - s) / 2)

def lambdaUS (u s : ℝ) : ℝ := Real.exp ((u + s) / 2)

def XiGUS (u s : ℝ) : ℝ := (rhoUS u s)^2

def XiMUS (u s : ℝ) : ℝ := (lambdaUS u s)^2

def kappaUS (u : ℝ) : ℝ := Real.exp u

@[simp] theorem rhoUS_pos (u s : ℝ) : 0 < rhoUS u s :=
  Real.exp_pos _

@[simp] theorem lambdaUS_pos (u s : ℝ) : 0 < lambdaUS u s :=
  Real.exp_pos _

/-- Squaring the gravity scale gives exactly the common character times the negative
relative character. -/
theorem XiGUS_factorization (u s : ℝ) :
    XiGUS u s = kappaUS u * Real.exp (-s) := by
  unfold XiGUS rhoUS kappaUS
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Squaring the Maxwell scale gives exactly the common character times the positive
relative character. -/
theorem XiMUS_factorization (u s : ℝ) :
    XiMUS u s = kappaUS u * Real.exp s := by
  unfold XiMUS lambdaUS kappaUS
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The common positive character is literally `ρ λ=e^u`. -/
theorem rho_mul_lambda_eq_kappa (u s : ℝ) :
    rhoUS u s * lambdaUS u s = kappaUS u := by
  unfold rhoUS lambdaUS kappaUS
  rw [← Real.exp_add]
  congr 1
  ring


/-- The product of the two sector characters is exactly the square of the common character. -/
theorem Xi_product_eq_kappa_sq (u s : ℝ) :
    XiGUS u s * XiMUS u s = (kappaUS u)^2 := by
  unfold XiGUS XiMUS
  rw [← mul_pow, rho_mul_lambda_eq_kappa]

/-- Therefore the positive projective common scale is literally
`sqrt(Xi_G Xi_M)=κ=ρλ`. -/
theorem character_common_scale_sqrt (u s : ℝ) :
    Real.sqrt (XiGUS u s * XiMUS u s) = kappaUS u := by
  rw [Xi_product_eq_kappa_sq, Real.sqrt_sq_eq_abs]
  exact abs_of_pos (Real.exp_pos u)

/-- The common character cancels completely from the relative ratio. -/
theorem character_ratio_eq_exp_two (u s : ℝ) :
    XiMUS u s / XiGUS u s = Real.exp (2 * s) := by
  rw [XiMUS_factorization, XiGUS_factorization]
  have hku : kappaUS u ≠ 0 := ne_of_gt (Real.exp_pos u)
  have hem : Real.exp (-s) ≠ 0 := ne_of_gt (Real.exp_pos (-s))
  rw [mul_div_mul_left _ _ hku]
  rw [div_eq_iff hem]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The logarithmic character ratio recovers the relative coordinate exactly. -/
theorem relative_coordinate_recovered (u s : ℝ) :
    (1 / 2 : ℝ) * Real.log (XiMUS u s / XiGUS u s) = s := by
  rw [character_ratio_eq_exp_two, Real.log_exp]
  ring

/-- The projective defect of the actual sector characters is exactly `tanh s`. -/
theorem character_defect_is_tanh (u s : ℝ) :
    delta (XiMUS u s / XiGUS u s) = Real.tanh s := by
  rw [character_ratio_eq_exp_two]
  exact delta_exp_two s

/-- The common character is exchange-even while the relative ratio is exchange-inverted. -/
theorem character_exchange (u s : ℝ) :
    XiGUS u (-s) = XiMUS u s ∧
    XiMUS u (-s) = XiGUS u s := by
  constructor
  · rw [XiGUS_factorization, XiMUS_factorization]
    simp
  · rw [XiMUS_factorization, XiGUS_factorization]
    simp


/-- Lower-index Maxwell stress scales by `(λ/ρ)²` under constant
`(g,A) ↦ (ρ²g, λA)`.  This definition records only that forced scalar weight. -/
def maxwellStressScaleFactor (ρ λ : ℝ) : ℝ :=
  (λ / ρ)^2

/-- The relative parametrization gives `λ/ρ=e^s` exactly. -/
theorem lambdaUS_div_rhoUS (u s : ℝ) :
    lambdaUS u s / rhoUS u s = Real.exp s := by
  unfold lambdaUS rhoUS
  have hr : Real.exp ((u - s) / 2) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  rw [div_eq_iff hr, ← Real.exp_add]
  congr 1
  ring

/-- Hence the Maxwell stress weight is precisely `e^{2s}`, independent of the common scale. -/
theorem maxwellStressScaleFactor_US (u s : ℝ) :
    maxwellStressScaleFactor (rhoUS u s) (lambdaUS u s) =
      Real.exp (2 * s) := by
  rw [maxwellStressScaleFactor, lambdaUS_div_rhoUS]
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The common scale therefore cancels from the rescaled Einstein-Maxwell component equation. -/
theorem rescaled_field_equation_weight
    (u s G T : ℝ) :
    G = 8 * Real.pi *
        maxwellStressScaleFactor (rhoUS u s) (lambdaUS u s) * T ↔
      G = 8 * Real.pi * Real.exp (2 * s) * T := by
  rw [maxwellStressScaleFactor_US]

/-- On a nonzero electrovac component, the original and rescaled field equations are
simultaneously satisfied exactly at the relative fixed point `s=0`. -/
theorem rescaled_solution_preserving_iff
    (u s T : ℝ) (hT : T ≠ 0) :
    (8 * Real.pi * T =
      8 * Real.pi *
        maxwellStressScaleFactor (rhoUS u s) (lambdaUS u s) * T) ↔
      s = 0 := by
  rw [maxwellStressScaleFactor_US]
  have hc : 8 * Real.pi * T ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)) hT
  constructor
  · intro h
    have heq :
        8 * Real.pi * T =
          Real.exp (2 * s) * (8 * Real.pi * T) := by
      calc
        8 * Real.pi * T
            = 8 * Real.pi * Real.exp (2 * s) * T := h
        _ = Real.exp (2 * s) * (8 * Real.pi * T) := by ring
    have hscale : (1 : ℝ) = Real.exp (2 * s) := by
      apply mul_right_cancel₀ hc
      simpa using heq
    exact (exp_two_eq_one_iff s).mp hscale.symm
  · rintro rfl
    simp

/-- Equality of the two sector characters occurs at exactly one relative point. -/
theorem character_rest_iff_zero (u s : ℝ) :
    XiGUS u s = XiMUS u s ↔ s = 0 := by
  rw [XiGUS_factorization, XiMUS_factorization]
  have hku : kappaUS u ≠ 0 := ne_of_gt (Real.exp_pos u)
  constructor
  · intro h
    have he : Real.exp (-s) = Real.exp s := mul_left_cancel₀ hku h
    have hs : -s = s := Real.exp_injective he
    linarith
  · rintro rfl
    simp

/-! ### Four-dimensional Maxwell trace and Einstein trace closure -/

/-- Algebraic trace factor of the Maxwell stress tensor in D dimensions, suppressing
the common nonzero normalization.  It is the contraction
`F^{ac}F_{ac} - (D/4) F^{cd}F_{cd}`. -/
def maxwellStressTraceFactor (D Fsq : ℝ) : ℝ :=
  (1 - D / 4) * Fsq

/-- Maxwell stress is identically trace-free in four dimensions. -/
@[simp] theorem maxwellStressTraceFactor_four (Fsq : ℝ) :
    maxwellStressTraceFactor 4 Fsq = 0 := by
  simp [maxwellStressTraceFactor]

/-- For a non-null invariant component, trace-freeness itself singles out four dimensions. -/
theorem maxwellStressTraceFactor_zero_iff_four
    (D Fsq : ℝ) (hF : Fsq ≠ 0) :
    maxwellStressTraceFactor D Fsq = 0 ↔ D = 4 := by
  unfold maxwellStressTraceFactor
  constructor
  · intro h
    have hf : 1 - D / 4 = 0 :=
      (mul_eq_zero.mp h).resolve_right hF
    linarith
  · rintro rfl
    norm_num

/-- Trace of the D-dimensional Einstein tensor. -/
def einsteinTrace (D scalarR : ℝ) : ℝ :=
  (1 - D / 2) * scalarR

/-- In four dimensions, a trace-free source and the traced Einstein equation force
vanishing scalar curvature. -/
theorem four_dimensional_tracefree_einstein_scalar_zero
    (scalarR traceT : ℝ)
    (htracefree : traceT = 0)
    (hEinTrace : einsteinTrace 4 scalarR = 8 * Real.pi * traceT) :
    scalarR = 0 := by
  rw [htracefree] at hEinTrace
  unfold einsteinTrace at hEinTrace
  norm_num at hEinTrace
  linarith

/-- Once the scalar curvature vanishes, the component Einstein equation reduces exactly
to `Ric = 8π T`. -/
theorem einstein_component_to_ricci
    (Ric metricComp scalarR T : ℝ)
    (hR : scalarR = 0)
    (hEin :
      Ric - (1 / 2 : ℝ) * metricComp * scalarR =
        8 * Real.pi * T) :
    Ric = 8 * Real.pi * T := by
  rw [hR] at hEin
  simpa using hEin

/-- Full scalar certificate of the Einstein-Maxwell trace closure:
Maxwell trace-freeness plus the traced and component Einstein equations force
`Ric = 8πT`, with no independent Ricci-stress hypothesis. -/
theorem einstein_maxwell_ricci_forced
    (Ric metricComp scalarR traceT T : ℝ)
    (htracefree : traceT = 0)
    (hEinTrace : einsteinTrace 4 scalarR = 8 * Real.pi * traceT)
    (hEin :
      Ric - (1 / 2 : ℝ) * metricComp * scalarR =
        8 * Real.pi * T) :
    Ric = 8 * Real.pi * T := by
  have hR :=
    four_dimensional_tracefree_einstein_scalar_zero
      scalarR traceT htracefree hEinTrace
  exact einstein_component_to_ricci Ric metricComp scalarR T hR hEin

/-- Therefore the fixed-point jet-curvature identity is forced directly from the
four-dimensional Einstein-Maxwell equations. -/
theorem jet_eq_minus_two_ricci_from_einstein_maxwell
    (Ric metricComp scalarR traceT T : ℝ)
    (htracefree : traceT = 0)
    (hEinTrace : einsteinTrace 4 scalarR = 8 * Real.pi * traceT)
    (hEin :
      Ric - (1 / 2 : ℝ) * metricComp * scalarR =
        8 * Real.pi * T) :
    -16 * Real.pi * T = -2 * Ric := by
  have hRic :=
    einstein_maxwell_ricci_forced
      Ric metricComp scalarR traceT T htracefree hEinTrace hEin
  rw [hRic]
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

/-- The field-equation fixed point is an exact iff for every nonzero electrovac component. -/
theorem solution_preserving_fixed_point_iff
    (t s : ℝ) (ht : t ≠ 0) :
    t = Real.exp (2 * s) * t ↔ s = 0 := by
  constructor
  · exact solution_preserving_fixed_point t s ht
  · rintro rfl
    simp

/-- Scalar component of the common-character-removed field-equation residual. -/
def scaledResidual (G T s : ℝ) : ℝ :=
  Real.exp (-s) * (G - 8 * Real.pi * Real.exp (2 * s) * T)

/-- On shell, the scaled residual is forced to the exchange-odd sinh defect used in the paper. -/
theorem scaledResidual_onShell_eq_sinh
    (G T s : ℝ) (hEinstein : G = 8 * Real.pi * T) :
    scaledResidual G T s = -16 * Real.pi * Real.sinh s * T := by
  have hexp : Real.exp (-s) * Real.exp (2 * s) = Real.exp s := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [scaledResidual, hEinstein]
  calc
    Real.exp (-s) *
        (8 * Real.pi * T - 8 * Real.pi * Real.exp (2 * s) * T)
        =
      8 * Real.pi * T *
        (Real.exp (-s) - Real.exp (-s) * Real.exp (2 * s)) := by ring
    _ = 8 * Real.pi * T * (Real.exp (-s) - Real.exp s) := by rw [hexp]
    _ = -16 * Real.pi * Real.sinh s * T := by
      rw [← Real.cosh_sub_sinh s, ← Real.cosh_add_sinh s]
      ring

/-- Scalar model of the on-shell odd normal defect. -/
def defect (T s : ℝ) : ℝ := -16 * Real.pi * Real.sinh s * T


/-- The odd defect formula is forced directly from the on-shell Einstein-Maxwell equation
and the relative Maxwell character; it is not an independent ansatz. -/
theorem defect_from_on_shell_equation
    (G T s : ℝ)
    (hEinstein : G = 8 * Real.pi * T) :
    Real.exp (-s) * (G - 8 * Real.pi * Real.exp (2 * s) * T) =
      defect T s := by
  rw [hEinstein]
  unfold defect
  rw [Real.sinh_eq]
  have he : Real.exp (-s) * Real.exp (2 * s) = Real.exp s := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- Conversely, the factorized residual and the hyperbolic odd carrier are exactly the same
on-shell object for every relative coordinate. -/
theorem defect_factorization_identity
    (T s : ℝ) :
    Real.exp (-s) *
        (8 * Real.pi * T - 8 * Real.pi * Real.exp (2 * s) * T) =
      -16 * Real.pi * Real.sinh s * T := by
  simpa [defect] using
    defect_from_on_shell_equation (8 * Real.pi * T) T s rfl

/-- The paper's defect is exactly the on-shell scaled field-equation residual. -/
theorem scaledResidual_onShell_eq_defect
    (G T s : ℝ) (hEinstein : G = 8 * Real.pi * T) :
    scaledResidual G T s = defect T s := by
  rw [scaledResidual_onShell_eq_sinh G T s hEinstein]
  rfl

@[simp] theorem defect_zero (T : ℝ) : defect T 0 = 0 := by
  simp [defect]

/-- On the nonvacuum sector, the odd defect itself has exactly the same unique zero. -/
theorem defect_eq_zero_iff
    (T s : ℝ) (hT : T ≠ 0) :
    defect T s = 0 ↔ s = 0 := by
  unfold defect
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  simp [hT, hpi, Real.sinh_eq_zero]

/-- The normal derivative of the on-shell defect at the fixed point is `-16πT`. -/
theorem defect_hasDerivAt_zero (T : ℝ) :
    HasDerivAt (defect T) (-16 * Real.pi * T) 0 := by
  unfold defect
  have h := (Real.hasDerivAt_sinh 0).const_mul (-16 * Real.pi)
  have h' := h.mul_const T
  simpa [mul_assoc, mul_left_comm, mul_comm] using h'


/-- On the nonvacuum sector the surviving first jet is genuinely nonzero. -/
theorem defect_first_jet_ne_zero
    (T : ℝ) (hT : T ≠ 0) :
    -16 * Real.pi * T ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)) hT

/-- The actual scaled Einstein-Maxwell residual has that same nonzero normal derivative on shell. -/
theorem scaledResidual_hasDerivAt_zero
    (G T : ℝ) (hEinstein : G = 8 * Real.pi * T) :
    HasDerivAt (scaledResidual G T) (-16 * Real.pi * T) 0 := by
  have hfun : scaledResidual G T = defect T := by
    funext s
    exact scaledResidual_onShell_eq_defect G T s hEinstein
  rw [hfun]
  exact defect_hasDerivAt_zero T

/-- Every even normal derivative of the odd on-shell defect vanishes at the fixed point. -/
theorem defect_even_iteratedDeriv_zero (T : ℝ) (n : ℕ) :
    iteratedDeriv (2 * n) (defect T) 0 = 0 := by
  have hfun : defect T = fun s : ℝ => (-16 * Real.pi * T) * Real.sinh s := by
    funext s
    unfold defect
    ring
  rw [hfun, iteratedDeriv_const_mul_field, Real.iteratedDeriv_even_sinh]
  simp

/-- Every odd normal derivative of the odd on-shell defect is the same surviving carrier.
Thus the entire odd jet tower lies on the single line generated by the first jet. -/
theorem defect_odd_iteratedDeriv_carrier (T : ℝ) (n : ℕ) :
    iteratedDeriv (2 * n + 1) (defect T) 0 = -16 * Real.pi * T := by
  have hfun : defect T = fun s : ℝ => (-16 * Real.pi * T) * Real.sinh s := by
    funext s
    unfold defect
    ring
  rw [hfun, iteratedDeriv_const_mul_field, Real.iteratedDeriv_odd_sinh]
  simp

/-- The full defect jet tower is therefore parity-rigid at relative rest. -/
theorem defect_full_jet_parity (T : ℝ) (n : ℕ) :
    iteratedDeriv (2 * n) (defect T) 0 = 0 ∧
    iteratedDeriv (2 * n + 1) (defect T) 0 = -16 * Real.pi * T :=
  ⟨defect_even_iteratedDeriv_zero T n, defect_odd_iteratedDeriv_carrier T n⟩

/-- The all-orders parity statement belongs to the on-shell field-equation residual itself. -/
theorem scaledResidual_full_jet_parity
    (G T : ℝ) (hEinstein : G = 8 * Real.pi * T) (n : ℕ) :
    iteratedDeriv (2 * n) (scaledResidual G T) 0 = 0 ∧
    iteratedDeriv (2 * n + 1) (scaledResidual G T) 0 = -16 * Real.pi * T := by
  have hfun : scaledResidual G T = defect T := by
    funext s
    exact scaledResidual_onShell_eq_defect G T s hEinstein
  rw [hfun]
  exact defect_full_jet_parity T n

/-- If the Einstein-Maxwell trace equation gives `Ric = 8πT`, then the fixed-point jet is `-2 Ric`. -/
theorem jet_eq_minus_two_ricci
    (T Ric : ℝ) (hRic : Ric = 8 * Real.pi * T) :
    -16 * Real.pi * T = -2 * Ric := by
  rw [hRic]
  ring

/-- Every odd defect jet is therefore exactly the same curvature carrier `-2 Ric`. -/
theorem defect_odd_iteratedDeriv_eq_minus_two_ricci
    (T Ric : ℝ) (hRic : Ric = 8 * Real.pi * T) (n : ℕ) :
    iteratedDeriv (2 * n + 1) (defect T) 0 = -2 * Ric := by
  rw [defect_odd_iteratedDeriv_carrier, jet_eq_minus_two_ricci T Ric hRic]

/-- Nonzero Ricci carrier means every odd normal jet genuinely survives freezing. -/
theorem defect_odd_iteratedDeriv_ne_zero
    (T Ric : ℝ) (hRic : Ric = 8 * Real.pi * T) (hRic0 : Ric ≠ 0) (n : ℕ) :
    iteratedDeriv (2 * n + 1) (defect T) 0 ≠ 0 := by
  rw [defect_odd_iteratedDeriv_eq_minus_two_ricci T Ric hRic n]
  exact mul_ne_zero (by norm_num) hRic0

/-- Every odd jet of the actual on-shell residual is the same curvature carrier `-2 Ric`. -/
theorem scaledResidual_odd_iteratedDeriv_eq_minus_two_ricci
    (G T Ric : ℝ)
    (hEinstein : G = 8 * Real.pi * T)
    (hRic : Ric = 8 * Real.pi * T)
    (n : ℕ) :
    iteratedDeriv (2 * n + 1) (scaledResidual G T) 0 = -2 * Ric := by
  have hfun : scaledResidual G T = defect T := by
    funext s
    exact scaledResidual_onShell_eq_defect G T s hEinstein
  rw [hfun]
  exact defect_odd_iteratedDeriv_eq_minus_two_ricci T Ric hRic n


/-- The same all-orders curvature statement with `Ric=8πT` derived, rather than assumed,
from the four-dimensional trace-free Einstein-Maxwell equations. -/
theorem scaledResidual_odd_iteratedDeriv_eq_minus_two_ricci_from_EM
    (G T Ric metricComp scalarR traceT : ℝ)
    (hEinstein : G = 8 * Real.pi * T)
    (htracefree : traceT = 0)
    (hEinTrace : einsteinTrace 4 scalarR = 8 * Real.pi * traceT)
    (hEinComp :
      Ric - (1 / 2 : ℝ) * metricComp * scalarR =
        8 * Real.pi * T)
    (n : ℕ) :
    iteratedDeriv (2 * n + 1) (scaledResidual G T) 0 = -2 * Ric := by
  have hRic :=
    einstein_maxwell_ricci_forced
      Ric metricComp scalarR traceT T htracefree hEinTrace hEinComp
  exact scaledResidual_odd_iteratedDeriv_eq_minus_two_ricci
    G T Ric hEinstein hRic n

/-- The first surviving normal jet of the actual on-shell residual is therefore exactly
`-2 Ric` from the Einstein-Maxwell equations themselves. -/
theorem scaledResidual_first_jet_eq_minus_two_ricci_from_EM
    (G T Ric metricComp scalarR traceT : ℝ)
    (hEinstein : G = 8 * Real.pi * T)
    (htracefree : traceT = 0)
    (hEinTrace : einsteinTrace 4 scalarR = 8 * Real.pi * traceT)
    (hEinComp :
      Ric - (1 / 2 : ℝ) * metricComp * scalarR =
        8 * Real.pi * T) :
    deriv (scaledResidual G T) 0 = -2 * Ric := by
  have hder :=
    (scaledResidual_hasDerivAt_zero G T hEinstein).deriv
  have hjet :=
    jet_eq_minus_two_ricci_from_einstein_maxwell
      Ric metricComp scalarR traceT T htracefree hEinTrace hEinComp
  rw [hder, hjet]

/-- On nonvacuum electrovac, the scaled field-equation residual has the unique zero `s=0`. -/
theorem scaledResidual_zero_iff_fixed_point
    (G T s : ℝ) (hEinstein : G = 8 * Real.pi * T) (hT : T ≠ 0) :
    scaledResidual G T s = 0 ↔ s = 0 := by
  rw [scaledResidual_onShell_eq_defect G T s hEinstein]
  exact defect_eq_zero_iff T s hT

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

/-- The exchange-odd carrier has the same all-orders parity tower: all even jets vanish,
all odd jets equal its first fixed-point jet. -/
theorem carrierOdd_full_jet_parity (η : ℝ) (n : ℕ) :
    iteratedDeriv (2 * n) (carrierOdd η) 0 = 0 ∧
    iteratedDeriv (2 * n + 1) (carrierOdd η) 0 = -2 * η := by
  have hfun : carrierOdd η = fun s : ℝ => (-2 * η) * Real.sinh s := by
    funext s
    unfold carrierOdd
    ring
  constructor
  · rw [hfun, iteratedDeriv_const_mul_field, Real.iteratedDeriv_even_sinh]
    simp
  · rw [hfun, iteratedDeriv_const_mul_field, Real.iteratedDeriv_odd_sinh]
    simp

/-- Dually, the exchange-even carrier has constant even jets and vanishing odd jets at rest. -/
theorem carrierEven_full_jet_parity (η : ℝ) (n : ℕ) :
    iteratedDeriv (2 * n) (carrierEven η) 0 = 2 * η ∧
    iteratedDeriv (2 * n + 1) (carrierEven η) 0 = 0 := by
  have hfun : carrierEven η = fun s : ℝ => (2 * η) * Real.cosh s := by
    funext s
    unfold carrierEven
    ring
  constructor
  · rw [hfun, iteratedDeriv_const_mul_field, Real.iteratedDeriv_even_cosh]
    simp
  · rw [hfun, iteratedDeriv_const_mul_field, Real.iteratedDeriv_odd_cosh]
    simp

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

/-- Linearized solution residual on the two action-sector coefficients.
At a solution this is the scalar model of
`R^{lin}_Φ(x_G E_G+x_M E_M)=(x_G-x_M)R`. -/
def residualLinear (Ric : ℝ) : R2 →ₗ[ℝ] ℝ where
  toFun v := (v.1 - v.2) * Ric
  map_add' x y := by
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    simp
    ring
  map_smul' c x := by
    rcases x with ⟨x₁, x₂⟩
    simp
    ring

/-- Action-space boost generator in the `(E_G,E_M)` basis. -/
def YA (v : R2) : R2 := (-v.1, v.2)

/-- Exchange-even action direction. -/
def CA : R2 := (1, 1)

/-- Exchange-odd action direction. -/
def DA : R2 := (-1, 1)

/-- Exchange of the two action sectors.  In the `(E_G,E_M)` basis it swaps components. -/
def JA (v : R2) : R2 := (v.2, v.1)

@[simp] theorem JA_CA : JA CA = CA := by
  ext <;> norm_num [JA, CA]

@[simp] theorem JA_DA : JA DA = -DA := by
  ext <;> norm_num [JA, DA]

@[simp] theorem JA_sq (v : R2) : JA (JA v) = v := by
  rcases v with ⟨x, y⟩
  rfl

@[simp] theorem residualLinear_CA (Ric : ℝ) :
    residualLinear Ric CA = 0 := by
  norm_num [residualLinear, CA]

@[simp] theorem residualLinear_DA (Ric : ℝ) :
    residualLinear Ric DA = -2 * Ric := by
  norm_num [residualLinear, DA]
  ring

/-- The odd action direction maps exactly to the fixed-point carrier `J=-2R=-16πT`. -/
theorem residualLinear_DA_eq_jet
    (T Ric : ℝ) (hRic : Ric = 8 * Real.pi * T) :
    residualLinear Ric DA = -16 * Real.pi * T := by
  rw [residualLinear_DA, ← jet_eq_minus_two_ricci T Ric hRic]

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


/-- The action boosts form a genuine one-parameter representation. -/
theorem actionBoost_add (s t : ℝ) (v : R2) :
    actionBoost (s + t) v = actionBoost s (actionBoost t v) := by
  rcases v with ⟨x, y⟩
  ext <;> simp [actionBoost, Real.exp_add] <;> ring

/-- Negative rapidity is the inverse action boost. -/
theorem actionBoost_neg_inverse (s : ℝ) (v : R2) :
    actionBoost (-s) (actionBoost s v) = v := by
  rw [← actionBoost_add]
  simp [actionBoost]

/-- Exchange reverses the orientation of the action rapidity and nothing else. -/
theorem JA_actionBoost (s : ℝ) (v : R2) :
    JA (actionBoost s v) = actionBoost (-s) (JA v) := by
  rcases v with ⟨x, y⟩
  ext <;> simp [JA, actionBoost]

@[simp] theorem actionBoost_zero (v : R2) : actionBoost 0 v = v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [actionBoost]

/-- The first component of the closed action boost obeys the generator equation. -/
theorem actionBoost_fst_hasDerivAt (v : R2) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (actionBoost t v).1)
      (YA (actionBoost s v)).1 s := by
  rcases v with ⟨x, y⟩
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1) s :=
    (hasDerivAt_id s).neg
  have hexpneg :
      HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-s)) s := by
    simpa using (Real.hasDerivAt_exp (-s)).comp s hneg
  simpa [actionBoost, YA, mul_comm, mul_left_comm, mul_assoc] using
    hexpneg.mul_const x

/-- The second component of the closed action boost obeys the generator equation. -/
theorem actionBoost_snd_hasDerivAt (v : R2) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (actionBoost t v).2)
      (YA (actionBoost s v)).2 s := by
  rcases v with ⟨x, y⟩
  simpa [actionBoost, YA, mul_comm, mul_left_comm, mul_assoc] using
    (Real.hasDerivAt_exp s).mul_const y

/-- Componentwise, the finite action boost is exactly the integral curve of `YA`. -/
theorem actionBoost_generated_by_YA (v : R2) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (actionBoost t v).1)
        (YA (actionBoost s v)).1 s ∧
    HasDerivAt (fun t : ℝ => (actionBoost t v).2)
        (YA (actionBoost s v)).2 s :=
  ⟨actionBoost_fst_hasDerivAt v s, actionBoost_snd_hasDerivAt v s⟩

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

/-- Principal non-null Maxwell carrier magnitude. -/
def principalChi (E B : ℝ) : ℝ := 2 * (E^2 + B^2)

@[simp] theorem principalChi_nonneg (E B : ℝ) : 0 ≤ principalChi E B := by
  unfold principalChi
  positivity

/-- The carrier is strictly positive whenever the principal Maxwell field is nonzero. -/
theorem principalChi_pos
    (E B : ℝ) (h : E ≠ 0 ∨ B ≠ 0) :
    0 < principalChi E B := by
  unfold principalChi
  rcases h with hE | hB
  · nlinarith [sq_pos_of_ne_zero hE, sq_nonneg B]
  · nlinarith [sq_nonneg E, sq_pos_of_ne_zero hB]


/-- The principal Maxwell carrier vanishes exactly in the vacuum principal frame. -/
theorem principalChi_eq_zero_iff (E B : ℝ) :
    principalChi E B = 0 ↔ E = 0 ∧ B = 0 := by
  constructor
  · intro h
    unfold principalChi at h
    have hs : E^2 + B^2 = 0 := by nlinarith
    constructor
    · nlinarith [sq_nonneg E, sq_nonneg B]
    · nlinarith [sq_nonneg E, sq_nonneg B]
  · rintro ⟨rfl, rfl⟩
    norm_num [principalChi]

/-- The two Maxwell invariants square exactly to the square of the principal carrier. -/
theorem maxwell_invariants_eq_principalChi_sq (E B : ℝ) :
    (maxwellI E B)^2 + (maxwellJ E B)^2 = (principalChi E B)^2 := by
  rw [maxwell_invariant_square]
  unfold principalChi
  ring

/-- Once the clock satisfies `ω²=χ`, its fourth power is exactly the invariant Maxwell magnitude. -/
theorem maxwell_clock_fourth_power
    (E B ω : ℝ)
    (hω : ω^2 = principalChi E B) :
    ω^4 = (maxwellI E B)^2 + (maxwellJ E B)^2 := by
  calc
    ω^4 = (ω^2)^2 := by ring
    _ = (principalChi E B)^2 := by rw [hω]
    _ = (maxwellI E B)^2 + (maxwellJ E B)^2 :=
      (maxwell_invariants_eq_principalChi_sq E B).symm

/-! ### Explicit principal Maxwell two-form and stress tensor -/

/-- Diagonal Minkowski sign in the principal orthonormal frame, signature `(-,+,+,+)`. -/
def principalMetricSign (i : Fin 4) : ℝ :=
  if i = 0 then -1 else 1

/-- Covariant components of `F = E e⁰∧e¹ + B e²∧e³`. -/
def principalMaxwellF (E B : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 1 then E
  else if i = 1 ∧ j = 0 then -E
  else if i = 2 ∧ j = 3 then B
  else if i = 3 ∧ j = 2 then -B
  else 0

/-- The explicit principal two-form is antisymmetric. -/
theorem principalMaxwellF_skew (E B : ℝ) (i j : Fin 4) :
    principalMaxwellF E B i j = - principalMaxwellF E B j i := by
  fin_cases i <;> fin_cases j <;> simp [principalMaxwellF]


/-- Lorentzian Hodge dual of the principal Maxwell two-form:
`⋆F = B e⁰∧e¹ - E e²∧e³`. -/
def principalMaxwellStarF (E B : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 1 then B
  else if i = 1 ∧ j = 0 then -B
  else if i = 2 ∧ j = 3 then -E
  else if i = 3 ∧ j = 2 then E
  else 0

/-- The Hodge-dual two-form is antisymmetric. -/
theorem principalMaxwellStarF_skew (E B : ℝ) (i j : Fin 4) :
    principalMaxwellStarF E B i j =
      - principalMaxwellStarF E B j i := by
  fin_cases i <;> fin_cases j <;> simp [principalMaxwellStarF]

/-- On Lorentzian two-forms the principal Hodge star squares to minus the identity. -/
theorem principalMaxwellStar_sq (E B : ℝ) :
    principalMaxwellStarF B (-E) = - principalMaxwellF E B := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [principalMaxwellStarF, principalMaxwellF]

/-- Direct contraction `F_ab (⋆F)^ab` in the principal orthonormal frame. -/
def principalMaxwellFStarF (E B : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    principalMetricSign i * principalMetricSign j *
      principalMaxwellF E B i j *
      principalMaxwellStarF E B i j

/-- The explicit field/dual contraction is exactly `-4EB`. -/
theorem principalMaxwellFStarF_eq_maxwellJ (E B : ℝ) :
    principalMaxwellFStarF E B = maxwellJ E B := by
  simp [principalMaxwellFStarF, principalMetricSign,
    principalMaxwellF, principalMaxwellStarF, maxwellJ]
  ring

/-- Direct contraction `F_ab F^ab` in the principal orthonormal frame. -/
def principalMaxwellFsq (E B : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    principalMetricSign i * principalMetricSign j *
      principalMaxwellF E B i j * principalMaxwellF E B i j

/-- The explicit contraction reproduces the invariant `2(B²-E²)`. -/
theorem principalMaxwellFsq_eq_maxwellI (E B : ℝ) :
    principalMaxwellFsq E B = maxwellI E B := by
  simp [principalMaxwellFsq, principalMetricSign, principalMaxwellF, maxwellI]
  ring


/-- Both scalar Maxwell invariants are therefore recovered directly from `F` and `⋆F`. -/
theorem principalMaxwell_invariants_from_forms (E B : ℝ) :
    principalMaxwellFsq E B = maxwellI E B ∧
    principalMaxwellFStarF E B = maxwellJ E B :=
  ⟨principalMaxwellFsq_eq_maxwellI E B,
    principalMaxwellFStarF_eq_maxwellJ E B⟩

/-- Their invariant magnitude is the square of the field-derived carrier. -/
theorem principalMaxwell_form_invariant_magnitude (E B : ℝ) :
    (principalMaxwellFsq E B)^2 +
      (principalMaxwellFStarF E B)^2 =
      (principalChi E B)^2 := by
  rw [principalMaxwellFsq_eq_maxwellI,
    principalMaxwellFStarF_eq_maxwellJ,
    maxwell_invariants_eq_principalChi_sq]

/-- Mixed Maxwell stress computed directly from the explicit two-form:
`T^a_b=(4π)⁻¹(F^{ac}F_{bc}-(1/4)δ^a_b F²)`. -/
def principalStressFromF (E B : ℝ) (i j : Fin 4) : ℝ :=
  (1 / (4 * Real.pi)) *
    (principalMetricSign i *
        (∑ c : Fin 4,
          principalMaxwellF E B i c *
            principalMetricSign c *
            principalMaxwellF E B j c)
      - (1 / 4 : ℝ) * (if i = j then 1 else 0) * maxwellI E B)

/-- Principal electromagnetic energy density from the explicit field. -/
def principalFieldEnergyDensity (E B : ℝ) : ℝ :=
  (E^2 + B^2) / (8 * Real.pi)

/-- A canonical principal-frame mixed Maxwell stress endomorphism, with overall scale `u`. -/
def principalStress (u : ℝ) : Fin 4 → Fin 4 → ℝ := fun i j =>
  if i = j then
    if i = 0 ∨ i = 1 then -u else u
  else 0

/-- Computing the Maxwell stress from `F` forces the canonical diagonal principal form. -/
theorem principalStressFromF_eq_principalStress
    (E B : ℝ) (i j : Fin 4) :
    principalStressFromF E B i j =
      principalStress (principalFieldEnergyDensity E B) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [principalStressFromF, principalStress, principalFieldEnergyDensity,
      principalMetricSign, principalMaxwellF, maxwellI] <;>
    field_simp [ne_of_gt Real.pi_pos] <;>
    ring

/-- The stress eigenvalue scale is exactly `χ/(16π)` because `χ=2(E²+B²)`. -/
theorem principalFieldEnergyDensity_eq_chi
    (E B : ℝ) :
    principalFieldEnergyDensity E B =
      principalChi E B / (16 * Real.pi) := by
  unfold principalFieldEnergyDensity principalChi
  field_simp [ne_of_gt Real.pi_pos]
  ring

/-- Direct principal-frame Rainich square identity. -/
theorem principalStress_sq (u : ℝ) (i j : Fin 4) :
    (∑ k : Fin 4, principalStress u i k * principalStress u k j) =
      (if i = j then u^2 else 0) := by
  fin_cases i <;> fin_cases j <;>
    simp [principalStress] <;> ring


/-- Trace of the squared principal endomorphism. -/
def principalStressTraceSq (u : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ k : Fin 4,
    principalStress u i k * principalStress u k i

/-- In four dimensions the squared trace is exactly four times the Rainich eigenvalue square. -/
theorem principalStress_trace_sq (u : ℝ) :
    principalStressTraceSq u = 4 * u^2 := by
  unfold principalStressTraceSq
  simp_rw [principalStress_sq]
  norm_num


/-- Since the fixed-point jet is `J=-2R`, the principal Ricci endomorphism is
`R=-J/2`; its squared trace is therefore one quarter of the jet squared trace. -/
def principalRicciNormFromCarrier (χ : ℝ) : ℝ :=
  (1 / 4 : ℝ) * principalStressTraceSq χ

/-- The Einstein-Maxwell Rainich carrier forces the Ricci norm to be exactly `χ²`. -/
theorem principalRicciNormFromCarrier_eq (χ : ℝ) :
    principalRicciNormFromCarrier χ = χ^2 := by
  rw [principalRicciNormFromCarrier, principalStress_trace_sq]
  ring

/-- Literal principal-frame form of
`J^a{}_c J^c{}_b = (1/4) tr(J²) δ^a{}_b`. -/
theorem principalStress_rainich (u : ℝ) (i j : Fin 4) :
    (∑ k : Fin 4, principalStress u i k * principalStress u k j) =
      (1 / 4 : ℝ) * principalStressTraceSq u * (if i = j then 1 else 0) := by
  rw [principalStress_sq, principalStress_trace_sq]
  by_cases h : i = j <;> simp [h] <;> ring


/-! ### Rainich carrier derived directly from the explicit Maxwell two-form -/

/-- Mixed trace of the Maxwell stress computed from the explicit principal two-form. -/
def principalStressFromFTrace (E B : ℝ) : ℝ :=
  ∑ i : Fin 4, principalStressFromF E B i i

/-- Maxwell stress is trace-free directly at the explicit field level. -/
theorem principalStressFromF_trace_zero (E B : ℝ) :
    principalStressFromFTrace E B = 0 := by
  unfold principalStressFromFTrace
  simp_rw [principalStressFromF_eq_principalStress]
  simp [principalStress, principalFieldEnergyDensity]

/-- Squared trace of the explicit Maxwell stress endomorphism. -/
def principalStressFromFTraceSq (E B : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ k : Fin 4,
    principalStressFromF E B i k * principalStressFromF E B k i

/-- Its squared trace is fixed by the principal field energy density. -/
theorem principalStressFromF_trace_sq (E B : ℝ) :
    principalStressFromFTraceSq E B =
      4 * (principalFieldEnergyDensity E B)^2 := by
  unfold principalStressFromFTraceSq
  simp_rw [principalStressFromF_eq_principalStress]
  exact principalStress_trace_sq (principalFieldEnergyDensity E B)

/-- The Rainich square identity is therefore a theorem of the explicit Maxwell two-form. -/
theorem principalStressFromF_rainich
    (E B : ℝ) (i j : Fin 4) :
    (∑ k : Fin 4,
      principalStressFromF E B i k * principalStressFromF E B k j) =
      (1 / 4 : ℝ) * principalStressFromFTraceSq E B *
        (if i = j then 1 else 0) := by
  simp_rw [principalStressFromF_eq_principalStress]
  rw [principalStressFromF_trace_sq]
  rw [principalStress_sq]
  by_cases h : i = j <;> simp [h] <;> ring

/-- Fixed-point jet matrix obtained from the field equation survivor
`J=-16π T^{EM}`. -/
def principalJetFromF (E B : ℝ) (i j : Fin 4) : ℝ :=
  -16 * Real.pi * principalStressFromF E B i j

/-- The explicit field-derived jet is the sign-reversed canonical carrier of magnitude `χ`. -/
theorem principalJetFromF_eq_neg_principalStress
    (E B : ℝ) (i j : Fin 4) :
    principalJetFromF E B i j =
      - principalStress (principalChi E B) i j := by
  rw [principalJetFromF, principalStressFromF_eq_principalStress,
    principalFieldEnergyDensity_eq_chi]
  by_cases hij : i = j
  · subst j
    fin_cases i <;>
      simp [principalStress] <;>
      field_simp [ne_of_gt Real.pi_pos] <;>
      ring
  · simp [principalStress, hij]

/-- The field-derived fixed-point jet satisfies `J²=χ² I` directly. -/
theorem principalJetFromF_sq
    (E B : ℝ) (i j : Fin 4) :
    (∑ k : Fin 4,
      principalJetFromF E B i k * principalJetFromF E B k j) =
      (if i = j then (principalChi E B)^2 else 0) := by
  simp_rw [principalJetFromF_eq_neg_principalStress]
  simpa using principalStress_sq (principalChi E B) i j

/-- Equivalently, the invariant Rainich normalization of the actual fixed-point jet is
the principal Maxwell carrier `χ=2(E²+B²)`. -/
theorem principalJetFromF_rainich
    (E B : ℝ) (i j : Fin 4) :
    (∑ k : Fin 4,
      principalJetFromF E B i k * principalJetFromF E B k j) =
      (principalChi E B)^2 * (if i = j then 1 else 0) := by
  rw [principalJetFromF_sq]
  by_cases h : i = j <;> simp [h]


/-! ### Explicit principal Einstein-Maxwell jet and Lorentzian plane -/

/-- Standard coordinate basis in the four-dimensional principal frame. -/
def principalBasis (i : Fin 4) : Fin 4 → ℝ :=
  fun j => if j = i then 1 else 0


/-- Action of the principal mixed Maxwell stress endomorphism on a vector. -/
def principalStressApply (u : ℝ) (v : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  ∑ j : Fin 4, principalStress u i j * v j

/-- The principal timelike direction is an eigenvector with eigenvalue `-u`. -/
theorem principalStress_time_eigen (u : ℝ) :
    principalStressApply u (principalBasis 0) =
      (-u) • principalBasis 0 := by
  funext i
  fin_cases i <;> simp [principalStressApply, principalStress, principalBasis]

/-- The principal longitudinal spacelike direction carries the same mixed eigenvalue. -/
theorem principalStress_space_eigen (u : ℝ) :
    principalStressApply u (principalBasis 1) =
      (-u) • principalBasis 1 := by
  funext i
  fin_cases i <;> simp [principalStressApply, principalStress, principalBasis]

/-- Einstein-Maxwell identifies the positive principal stress magnitude with `χ/(16π)`. -/
def principalEnergyDensity (χ : ℝ) : ℝ :=
  χ / (16 * Real.pi)

/-- The timelike principal Maxwell eigenvalue is therefore exactly `-χ/(16π)`. -/
theorem principalMaxwell_timelike_eigen_from_chi (χ : ℝ) :
    principalStressApply (principalEnergyDensity χ) (principalBasis 0) =
      (-χ / (16 * Real.pi)) • principalBasis 0 := by
  rw [principalStress_time_eigen]
  congr 1
  unfold principalEnergyDensity
  ring

/-- Positive carrier magnitude forces positive principal electromagnetic energy density. -/
theorem principalEnergyDensity_pos
    (χ : ℝ) (hχ : 0 < χ) :
    0 < principalEnergyDensity χ := by
  unfold principalEnergyDensity
  positivity

/-- And the carrier is recovered exactly from that energy density. -/
theorem principalEnergyDensity_recovers_chi (χ : ℝ) :
    16 * Real.pi * principalEnergyDensity χ = χ := by
  unfold principalEnergyDensity
  field_simp [ne_of_gt Real.pi_pos]

/-- Minkowski quadratic form in the principal orthonormal frame. -/
def principalMinkowskiSq (v : Fin 4 → ℝ) : ℝ :=
  -(v 0)^2 + (v 1)^2 + (v 2)^2 + (v 3)^2

/-- The fixed-point jet is minus the principal Maxwell stress endomorphism, so its
Lorentzian principal plane carries the positive carrier eigenvalue. -/
def principalJetApply (u : ℝ) (v : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  if i = 0 ∨ i = 1 then u * v i else -u * v i

/-- The explicit jet is exactly `-T` in the principal frame. -/
theorem principalJetApply_eq_neg_stress
    (u : ℝ) (v : Fin 4 → ℝ) (i : Fin 4) :
    principalJetApply u v i =
      ∑ j : Fin 4, (- principalStress u i j) * v j := by
  fin_cases i <;> simp [principalJetApply, principalStress]

/-- Carrier normalization removes the magnitude and leaves the canonical involution. -/
def principalJetInvolution (v : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  if i = 0 ∨ i = 1 then v i else -v i


/-- Action of the actual field-derived fixed-point jet on a vector. -/
def principalJetFromFApply
    (E B : ℝ) (v : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  ∑ j : Fin 4, principalJetFromF E B i j * v j

/-- The actual `J=-16πT[F]` action is exactly the canonical carrier action of magnitude `χ`. -/
theorem principalJetFromFApply_eq_principalJetApply
    (E B : ℝ) (v : Fin 4 → ℝ) :
    principalJetFromFApply E B v =
      principalJetApply (principalChi E B) v := by
  funext i
  unfold principalJetFromFApply
  rw [show
    (∑ j : Fin 4, principalJetFromF E B i j * v j) =
      ∑ j : Fin 4,
        (-principalStress (principalChi E B) i j) * v j by
      apply Finset.sum_congr rfl
      intro j hj
      rw [principalJetFromF_eq_neg_principalStress]]
  exact (principalJetApply_eq_neg_stress
    (principalChi E B) v i).symm

/-- Normalized action of the field-derived carrier. -/
def principalNormalizedJetFromFApply
    (E B : ℝ) (v : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  (principalChi E B)⁻¹ * principalJetFromFApply E B v i

/-- On the non-null Maxwell sector, normalizing the actual field-derived jet by its
invariant magnitude gives exactly the canonical Rainich involution. -/
theorem principalNormalizedJetFromFApply_eq_involution
    (E B : ℝ)
    (hchi : principalChi E B ≠ 0)
    (v : Fin 4 → ℝ) :
    principalNormalizedJetFromFApply E B v =
      principalJetInvolution v := by
  funext i
  rw [principalNormalizedJetFromFApply]
  have happ :
      principalJetFromFApply E B v i =
        principalJetApply (principalChi E B) v i := by
    exact congrFun (principalJetFromFApply_eq_principalJetApply E B v) i
  rw [happ]
  fin_cases i <;>
    simp [principalJetApply, principalJetInvolution, hchi] <;>
    field_simp [hchi]


/-- Projection onto the time/principal-space plane. -/
def principalLorentzPart (v : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  if i = 0 ∨ i = 1 then v i else 0

/-- Projection onto the transverse electromagnetic plane. -/
def principalTransversePart (v : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  if i = 0 ∨ i = 1 then 0 else v i

/-- The two principal planes reconstruct every vector exactly. -/
theorem principal_plane_decomposition (v : Fin 4 → ℝ) :
    principalLorentzPart v + principalTransversePart v = v := by
  funext i
  fin_cases i <;> simp [principalLorentzPart, principalTransversePart]

/-- The Lorentzian principal plane is exactly the +1 eigenspace of the normalized jet. -/
theorem principalLorentzPart_eigen_plus (v : Fin 4 → ℝ) :
    principalJetInvolution (principalLorentzPart v) =
      principalLorentzPart v := by
  funext i
  fin_cases i <;> simp [principalJetInvolution, principalLorentzPart]

/-- The transverse plane is exactly the -1 eigenspace of the normalized jet. -/
theorem principalTransversePart_eigen_minus (v : Fin 4 → ℝ) :
    principalJetInvolution (principalTransversePart v) =
      - principalTransversePart v := by
  funext i
  fin_cases i <;> simp [principalJetInvolution, principalTransversePart]

/-- The +1 plane is genuinely Lorentzian: it contains a unit timelike basis vector. -/
@[simp] theorem principal_time_basis_norm :
    principalMinkowskiSq (principalBasis 0) = -1 := by
  norm_num [principalMinkowskiSq, principalBasis]

/-- The same +1 plane contains an orthogonal unit spacelike principal direction. -/
@[simp] theorem principal_space_basis_norm :
    principalMinkowskiSq (principalBasis 1) = 1 := by
  norm_num [principalMinkowskiSq, principalBasis]

/-- Both time and principal-space basis vectors are fixed by the normalized jet. -/
theorem principal_lorentz_basis_eigen_plus :
    principalJetInvolution (principalBasis 0) = principalBasis 0 ∧
    principalJetInvolution (principalBasis 1) = principalBasis 1 := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [principalJetInvolution, principalBasis]

/-- The two transverse basis vectors have eigenvalue -1. -/
theorem principal_transverse_basis_eigen_minus :
    principalJetInvolution (principalBasis 2) = - principalBasis 2 ∧
    principalJetInvolution (principalBasis 3) = - principalBasis 3 := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [principalJetInvolution, principalBasis]


/-- Thus the explicit Maxwell field fixes the Lorentzian principal basis directions as
the +1 eigendirections of its normalized fixed-point jet. -/
theorem principalFieldDerived_lorentz_basis_eigen_plus
    (E B : ℝ)
    (hchi : principalChi E B ≠ 0) :
    principalNormalizedJetFromFApply E B (principalBasis 0) =
        principalBasis 0 ∧
    principalNormalizedJetFromFApply E B (principalBasis 1) =
        principalBasis 1 := by
  rw [principalNormalizedJetFromFApply_eq_involution E B hchi,
    principalNormalizedJetFromFApply_eq_involution E B hchi]
  exact principal_lorentz_basis_eigen_plus

/-- The transverse basis directions are simultaneously fixed with eigenvalue -1. -/
theorem principalFieldDerived_transverse_basis_eigen_minus
    (E B : ℝ)
    (hchi : principalChi E B ≠ 0) :
    principalNormalizedJetFromFApply E B (principalBasis 2) =
        - principalBasis 2 ∧
    principalNormalizedJetFromFApply E B (principalBasis 3) =
        - principalBasis 3 := by
  rw [principalNormalizedJetFromFApply_eq_involution E B hchi,
    principalNormalizedJetFromFApply_eq_involution E B hchi]
  exact principal_transverse_basis_eigen_minus

/-- The transverse principal plane is positive semidefinite for the Minkowski form. -/
theorem principalTransversePart_nonneg (v : Fin 4 → ℝ) :
    0 ≤ principalMinkowskiSq (principalTransversePart v) := by
  simp [principalMinkowskiSq, principalTransversePart]
  positivity

/-- Thus the sign-selected +1 eigenspace is the unique principal plane carrying both
timelike and spacelike directions in this canonical Maxwell frame. -/
theorem principal_plus_plane_lorentzian_certificate :
    principalJetInvolution (principalBasis 0) = principalBasis 0 ∧
    principalJetInvolution (principalBasis 1) = principalBasis 1 ∧
    principalMinkowskiSq (principalBasis 0) < 0 ∧
    0 < principalMinkowskiSq (principalBasis 1) := by
  refine ⟨principal_lorentz_basis_eigen_plus.1,
    principal_lorentz_basis_eigen_plus.2, ?_, ?_⟩ <;> norm_num


/-! ### Explicit local clock decomposition in the principal frame -/

/-- Chronometric covector `T_O=-û♭` in the canonical principal orthonormal frame. -/
def principalTO (v : Fin 4 → ℝ) : ℝ := v 0

/-- Chronometric unit timelike vector `û_*`. -/
def principalUhat : Fin 4 → ℝ := principalBasis 0

/-- Physical-metric unit vector `u_* = ω û_*` when `χ=ω²`. -/
def principalPhysicalU (ω : ℝ) : Fin 4 → ℝ :=
  ω • principalUhat

/-- Carrier endomorphism `J=χS=ω²S` in the normalized principal frame. -/
def principalJetFromRate (ω : ℝ) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => ω^2 * principalJetInvolution v i

/-- Spatial remainder after removing the forced timelike carrier component. -/
def principalSpatialRemainder (ω : ℝ) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  principalJetFromRate ω v -
    (ω * principalTO v) • principalPhysicalU ω

/-- Every carrier image splits exactly as
`Jv = ω T_O(v) u_* + w`. -/
theorem principalJet_local_decomposition
    (ω : ℝ) (v : Fin 4 → ℝ) :
    principalJetFromRate ω v =
      (ω * principalTO v) • principalPhysicalU ω +
        principalSpatialRemainder ω v := by
  unfold principalSpatialRemainder
  module

/-- The remainder is spatial: its time component vanishes identically. -/
theorem principalSpatialRemainder_time_zero
    (ω : ℝ) (v : Fin 4 → ℝ) :
    principalSpatialRemainder ω v 0 = 0 := by
  simp [principalSpatialRemainder, principalJetFromRate,
    principalJetInvolution, principalPhysicalU, principalUhat,
    principalTO, principalBasis]
  ring

/-- The scalar left after restricting the pointwise response to the principal rest
three-plane is proportional to `T_O(v)`. -/
def principalRestrictedResponse (ω : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  ω * principalTO v

/-- The normalized unit has response coefficient exactly `ω`. -/
@[simp] theorem principalRestrictedResponse_unit (ω : ℝ) :
    principalRestrictedResponse ω principalUhat = ω := by
  simp [principalRestrictedResponse, principalTO, principalUhat, principalBasis]

/-- Every restricted pointwise response factors through the unit response by the
chronometric covector and nothing else. -/
theorem principalRestrictedResponse_factor
    (ω : ℝ) (v : Fin 4 → ℝ) :
    principalRestrictedResponse ω v =
      principalTO v * principalRestrictedResponse ω principalUhat := by
  simp [principalRestrictedResponse]
  ring

/-- On the positive-rate sector, the ratio coefficient in the local Iyer-Wald response
is uniquely the chronometric covector value `T_O(v)`. -/
theorem principalLocalClockRatio_forced
    (ω λ : ℝ) (v : Fin 4 → ℝ) (hω : ω ≠ 0)
    (hresponse :
      principalRestrictedResponse ω v =
        λ * principalRestrictedResponse ω principalUhat) :
    λ = principalTO v := by
  rw [principalRestrictedResponse_unit] at hresponse
  unfold principalRestrictedResponse at hresponse
  apply mul_right_cancel₀ hω
  simpa [mul_comm] using hresponse.symm

/-- The local chronometric covector is normalized on the selected timelike unit. -/
@[simp] theorem principalTO_unit :
    principalTO principalUhat = 1 := by
  simp [principalTO, principalUhat, principalBasis]

/-- The invariant Rainich magnitude `χ = 1/2 sqrt(tr J²)` recovers the positive
principal eigenvalue exactly. -/
theorem principalStress_chi_from_trace
    (u : ℝ) (hu : 0 ≤ u) :
    (1 / 2 : ℝ) * Real.sqrt (principalStressTraceSq u) = u := by
  rw [principalStress_trace_sq]
  have hsq : 4 * u^2 = (2 * u)^2 := by ring
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  · ring
  · positivity

/-- If `J=-2R`, so the squared carrier norm is four times the Ricci norm, then the
same invariant normalization forces `χ = sqrt(K)`. -/
theorem carrier_chi_eq_sqrt_ricci_norm
    (Jnorm K : ℝ)
    (hK : 0 ≤ K)
    (hJ : Jnorm = 4 * K) :
    (1 / 2 : ℝ) * Real.sqrt Jnorm = Real.sqrt K := by
  have hsqrtK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hsquare : 4 * K = (2 * Real.sqrt K)^2 := by
    rw [mul_pow, Real.sq_sqrt hK]
    ring
  rw [hJ, hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  · ring
  · positivity

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


/-- At the zero-carrier boundary the same Rainich square law becomes nilpotence. -/
theorem rainich_square_nilpotent_at_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] V) (χ : ℝ)
    (hRainich : J.comp J = (χ^2) • LinearMap.id)
    (hχ : χ = 0) :
    J.comp J = 0 := by
  rw [hχ] at hRainich
  simpa using hRainich

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


/-- For a self-adjoint involution, the +1 and -1 eigenspaces are automatically orthogonal.
This is the algebraic core of the principal-plane splitting used after Rainich normalization. -/
theorem involution_eigenspaces_orthogonal
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (S : V →ₗ[ℝ] V)
    (hself : ∀ x y : V, B (S x) y = B x (S y))
    (x y : V) (hx : S x = x) (hy : S y = -y) :
    B x y = 0 := by
  have hneg : B x y = - B x y := by
    calc
      B x y = B (S x) y := by rw [hx]
      _ = B x (S y) := hself x y
      _ = B x (-y) := by rw [hy]
      _ = - B x y := by simp
  linarith

/-! ### Full-jet residual stabilizer logic -/

variable {G : Type*}

/-- Exact residual symmetry of the complete fixed-point jet is the intersection of all
finite-order stabilizers. -/
def fullJetStabilizer (H : ℕ → Set G) : Set G :=
  ⋂ n, H n

theorem fullJetStabilizer_subset (H : ℕ → Set G) (n : ℕ) :
    fullJetStabilizer H ⊆ H n := by
  intro g hg
  exact Set.mem_iInter.mp hg n

/-- If any finite jet order has only the identity stabilizer, then the full jet has only
that identity as well. -/
theorem fullJetStabilizer_eq_singleton_of_finite_break
    (H : ℕ → Set G) (e : G)
    (he : ∀ n, e ∈ H n)
    (m : ℕ) (hm : H m = {e}) :
    fullJetStabilizer H = {e} := by
  ext g
  constructor
  · intro hg
    have hgm : g ∈ H m := fullJetStabilizer_subset H m hg
    rw [hm] at hgm
    exact hgm
  · intro hg
    have hge : g = e := by simpa using hg
    subst g
    exact Set.mem_iInter.mpr he

/-- If no finite jet kills a transformation but it stabilizes every finite jet, then it
survives exactly as a full-jet residual symmetry. -/
theorem mem_fullJetStabilizer_iff
    (H : ℕ → Set G) (g : G) :
    g ∈ fullJetStabilizer H ↔ ∀ n, g ∈ H n := by
  simp [fullJetStabilizer]

/-! ## 6. Unique residual boost balance -/

/-- Principal-plane covector norm in a normalized null basis, with
`g^{-1}(p,p) = -2 q_- q_+`. -/
def nullCovectorNormSq (qminus qplus : ℝ) : ℝ :=
  -2 * qminus * qplus

/-- A non-null principal-plane covector necessarily has both null components nonzero. -/
theorem nullCovectorNormSq_ne_zero_components
    (qm qp : ℝ)
    (hnonnull : nullCovectorNormSq qm qp ≠ 0) :
    qm ≠ 0 ∧ qp ≠ 0 := by
  constructor
  · intro hqm
    apply hnonnull
    simp [nullCovectorNormSq, hqm]
  · intro hqp
    apply hnonnull
    simp [nullCovectorNormSq, hqp]


/-- The principal-plane norm is invariant under the residual null boost. -/
theorem nullCovectorNormSq_boost_invariant
    (qm qp τ : ℝ) :
    nullCovectorNormSq (Real.exp (-τ) * qm) (Real.exp τ * qp) =
      nullCovectorNormSq qm qp := by
  unfold nullCovectorNormSq
  rw [← mul_assoc, ← mul_assoc, ← Real.exp_add]
  have hz : -τ + τ = 0 := by ring
  rw [hz, Real.exp_zero]
  ring

/-- Therefore the geometric non-null condition does not depend on the starting null dyad. -/
theorem nullCovector_nonnull_boost_iff
    (qm qp τ : ℝ) :
    nullCovectorNormSq (Real.exp (-τ) * qm) (Real.exp τ * qp) ≠ 0 ↔
      nullCovectorNormSq qm qp ≠ 0 := by
  rw [nullCovectorNormSq_boost_invariant]

/-- Scalar boost defect. -/
def boostDefect (qminus qplus σ : ℝ) : ℝ :=
  Real.exp (-2 * σ) * qminus^2 - Real.exp (2 * σ) * qplus^2


/-- Boosted null components themselves. -/
def boostedQMinus (qminus σ : ℝ) : ℝ := Real.exp (-σ) * qminus
def boostedQPlus (qplus σ : ℝ) : ℝ := Real.exp σ * qplus

/-- Timelike/rest component of the principal-plane covector, up to the fixed null normalization. -/
def boostedRestComponent (qminus qplus σ : ℝ) : ℝ :=
  boostedQMinus qminus σ + boostedQPlus qplus σ

/-- The advertised balance rapidity. -/
def sigmaStar (qminus qplus : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (|qminus / qplus|)


/-- Exchanging the two principal null directions reverses the balancing orientation. -/
theorem sigmaStar_exchange
    (qm qp : ℝ) (hqm : qm ≠ 0) (hqp : qp ≠ 0) :
    sigmaStar qp qm = - sigmaStar qm qp := by
  unfold sigmaStar
  have hr : |qm / qp| ≠ 0 := abs_ne_zero.mpr (div_ne_zero hqm hqp)
  have hinv : |qp / qm| = (|qm / qp|)⁻¹ := by
    rw [abs_div, abs_div]
    field_simp [abs_ne_zero.mpr hqm, abs_ne_zero.mpr hqp]
  rw [hinv, Real.log_inv]
  ring

/-- Exchange reverses the boost defect together with rapidity orientation. -/
theorem boostDefect_exchange (qm qp σ : ℝ) :
    boostDefect qp qm (-σ) = - boostDefect qm qp σ := by
  unfold boostDefect
  ring_nf
  ring

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


/-- The manuscript's displayed derivative of the boost defect. -/
theorem boostDefect_hasDerivAt
    (qm qp σ : ℝ) :
    HasDerivAt (boostDefect qm qp)
      (-2 * (Real.exp (-2 * σ) * qm^2 + Real.exp (2 * σ) * qp^2)) σ := by
  have hm :
      HasDerivAt (fun x : ℝ => Real.exp (-2 * x))
        (-2 * Real.exp (-2 * σ)) σ := by
    convert (Real.hasDerivAt_exp (-2 * σ)).comp σ
      (hasDerivAt_const_mul (-2 : ℝ)) using 1 <;> ring
  have hp :
      HasDerivAt (fun x : ℝ => Real.exp (2 * x))
        (2 * Real.exp (2 * σ)) σ := by
    convert (Real.hasDerivAt_exp (2 * σ)).comp σ
      (hasDerivAt_const_mul (2 : ℝ)) using 1 <;> ring
  have h := (hm.mul_const (qm^2)).sub (hp.mul_const (qp^2))
  simpa [boostDefect] using h

/-- On the resolving non-null sector the defect derivative is strictly negative everywhere. -/
theorem boostDefect_derivative_negative
    (qm qp σ : ℝ) (hqm : qm ≠ 0) (hqp : qp ≠ 0) :
    -2 * (Real.exp (-2 * σ) * qm^2 + Real.exp (2 * σ) * qp^2) < 0 := by
  have hqm2 : 0 < qm^2 := sq_pos_of_ne_zero hqm
  have hqp2 : 0 < qp^2 := sq_pos_of_ne_zero hqp
  have h1 : 0 < Real.exp (-2 * σ) * qm^2 := mul_pos (Real.exp_pos _) hqm2
  have h2 : 0 < Real.exp (2 * σ) * qp^2 := mul_pos (Real.exp_pos _) hqp2
  nlinarith

/-- Vanishing rest component always implies boost balance. -/
theorem restComponent_zero_implies_balance
    (qm qp σ : ℝ)
    (hrest : boostedRestComponent qm qp σ = 0) :
    boostDefect qm qp σ = 0 := by
  have hs := boosted_component_squares qm qp σ
  rcases hs with ⟨hm, hp⟩
  unfold boostedRestComponent boostedQMinus boostedQPlus at hrest
  unfold boostDefect
  rw [← hm, ← hp]
  nlinarith

/-- For a spacelike principal-plane covector, boost balance forces zero timelike/rest component. -/
theorem balance_implies_restComponent_zero_of_spacelike
    (qm qp σ : ℝ)
    (hspace : 0 < nullCovectorNormSq qm qp)
    (hbal : boostDefect qm qp σ = 0) :
    boostedRestComponent qm qp σ = 0 := by
  let A := boostedQMinus qm σ
  let B := boostedQPlus qp σ
  have hs := boosted_component_squares qm qp σ
  have hsq : A^2 = B^2 := by
    rcases hs with ⟨hm, hp⟩
    unfold boostDefect at hbal
    unfold A B boostedQMinus boostedQPlus
    linarith
  have hab : A * B < 0 := by
    unfold A B boostedQMinus boostedQPlus
    unfold nullCovectorNormSq at hspace
    have he : 0 < Real.exp (-σ) * Real.exp σ := mul_pos (Real.exp_pos _) (Real.exp_pos _)
    have hq : qm * qp < 0 := by nlinarith
    nlinarith [mul_pos_of_pos_of_neg he hq]
  unfold boostedRestComponent
  change A + B = 0
  nlinarith [sq_nonneg (A + B), sq_nonneg (A - B)]

/-- Thus on the spacelike resolving sector the balance equation is exactly the
zero-radial-boost/rest-frame condition used in the Kerr-Newman specialization. -/
theorem balance_iff_restComponent_zero_of_spacelike
    (qm qp σ : ℝ)
    (hspace : 0 < nullCovectorNormSq qm qp) :
    boostDefect qm qp σ = 0 ↔ boostedRestComponent qm qp σ = 0 := by
  constructor
  · exact balance_implies_restComponent_zero_of_spacelike qm qp σ hspace
  · exact restComponent_zero_implies_balance qm qp σ

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


/-- A covector that is purely spatial/radial in the unboosted principal frame has opposite
null components and is balanced exactly at zero rapidity. -/
theorem opposite_null_components_balance_iff_zero
    (q σ : ℝ) (hq : q ≠ 0) :
    boostDefect q (-q) σ = 0 ↔ σ = 0 := by
  constructor
  · intro h
    apply boost_balance_unique q (-q) σ 0 hq (neg_ne_zero.mpr hq) h
    simp [boostDefect]
  · rintro rfl
    simp [boostDefect]

/-- The explicit balancing rapidity of opposite nonzero null components is therefore zero. -/
theorem sigmaStar_opposite_components
    (q : ℝ) (hq : q ≠ 0) :
    sigmaStar q (-q) = 0 := by
  exact (opposite_null_components_balance_iff_zero q (sigmaStar q (-q)) hq).mp
    (sigmaStar_balance q (-q) hq (neg_ne_zero.mpr hq))

/-- In the manuscript's geometric hypothesis `p² ≠ 0`, the unique balance follows from
one non-null condition rather than two separately imposed component assumptions. -/
theorem boost_balance_exists_unique_of_nonnull
    (qm qp : ℝ)
    (hnonnull : nullCovectorNormSq qm qp ≠ 0) :
    ∃! σ : ℝ, boostDefect qm qp σ = 0 := by
  rcases nullCovectorNormSq_ne_zero_components qm qp hnonnull with ⟨hqm, hqp⟩
  exact boost_balance_exists_unique qm qp hqm hqp

/-- The same non-null condition forces the manuscript's explicit balancing rapidity to solve
the defect equation. -/
theorem sigmaStar_balance_of_nonnull
    (qm qp : ℝ)
    (hnonnull : nullCovectorNormSq qm qp ≠ 0) :
    boostDefect qm qp (sigmaStar qm qp) = 0 := by
  rcases nullCovectorNormSq_ne_zero_components qm qp hnonnull with ⟨hqm, hqp⟩
  exact sigmaStar_balance qm qp hqm hqp

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


/-- Multiplication of the carrier by a positive constant leaves its logarithmic differential
coefficient unchanged.  This is the scalar algebra behind `d log(cχ)=d log χ`. -/
theorem logarithmic_differential_scale_invariant
    (c χ dχ : ℝ) (hc : c ≠ 0) (hχ : χ ≠ 0) :
    (c * dχ) / (c * χ) = dχ / χ := by
  field_simp [hc, hχ]
  ring

/-- In particular, the carrier gradient used to balance the residual boost is independent
of the common Einstein-Maxwell representative. -/
theorem logarithmic_differential_homothety_invariant
    (ρ χ dχ : ℝ) (hρ : ρ ≠ 0) (hχ : χ ≠ 0) :
    ((ρ⁻²) * dχ) / ((ρ⁻²) * χ) = dχ / χ := by
  apply logarithmic_differential_scale_invariant
  · exact inv_ne_zero (pow_ne_zero 2 hρ)
  · exact hχ

/-- Homogeneity and unit-involution normalization together force the conformal factor itself:
there is no residual positive multiplicative constant. -/
theorem conformal_factor_forced
    (f : ℝ → ℝ)
    (hhom : ∀ c χ : ℝ, 0 < c → 0 < χ → f (c * χ) = c * f χ)
    (χ : ℝ) (hχ : 0 < χ)
    (hC : 0 < f 1)
    (hunit : χ^2 / (f χ)^2 = 1) :
    f χ = χ := by
  have hlin : f χ = f 1 * χ :=
    homogeneous_conformal_factor f hhom χ hχ
  have hunit' : χ^2 / (f 1 * χ)^2 = 1 := by
    rw [← hlin]
    exact hunit
  have hCeq : f 1 = 1 :=
    unit_involution_fixes_conformal_constant (f 1) χ hC hχ hunit'
  rw [hlin, hCeq, one_mul]


/-! ### Chronometric normalization under the forced conformal metric -/

/-- Vector rescaling needed to keep a g-unit timelike vector unit after `ĝ=χg`. -/
def conformalUnitFactor (χ : ℝ) : ℝ :=
  (Real.sqrt χ)⁻¹

/-- On the positive carrier sector, the metric and vector rescalings cancel exactly. -/
theorem conformalUnitFactor_metric_cancel
    (χ : ℝ) (hχ : 0 < χ) :
    χ * (conformalUnitFactor χ)^2 = 1 := by
  have hs : (Real.sqrt χ)^2 = χ := Real.sq_sqrt (le_of_lt hχ)
  have hs0 : Real.sqrt χ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hχ)
  unfold conformalUnitFactor
  field_simp [hs0]
  nlinarith

/-- Therefore a unit timelike vector for `g` remains unit timelike after the forced
chronometric rescaling. -/
theorem conformal_unit_timelike_normalization
    (χ normg : ℝ)
    (hχ : 0 < χ)
    (hu : normg = -1) :
    χ * (conformalUnitFactor χ)^2 * normg = -1 := by
  rw [hu, conformalUnitFactor_metric_cancel χ hχ]
  ring

/-- Lowering the normalized vector with `ĝ=χg` contributes exactly one factor
of `sqrt χ`. -/
theorem conformal_dual_scale
    (χ : ℝ) (hχ : 0 < χ) :
    χ * conformalUnitFactor χ = Real.sqrt χ := by
  have hs0 : Real.sqrt χ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hχ)
  have hs : (Real.sqrt χ)^2 = χ := Real.sq_sqrt (le_of_lt hχ)
  unfold conformalUnitFactor
  field_simp [hs0]
  nlinarith

/-- With `ω=sqrt χ`, the local chronometric covector coefficient is exactly `ω`. -/
theorem conformal_dual_scale_eq_clock_rate
    (χ ω : ℝ) (hχ : 0 < χ) (hω : ω = Real.sqrt χ) :
    χ * conformalUnitFactor χ = ω := by
  rw [conformal_dual_scale χ hχ, hω]

/-! ### Conformal null-Hamiltonian transport -/

/-- Product-rule algebra for a conformally rescaled Hamiltonian `Ĥ=cH`: on the null cone
`H=0`, the differential is simply scaled by `c`. -/
theorem conformal_null_hamiltonian_differential
    (c H dc dH : ℝ) (hH : H = 0) :
    c * dH + H * dc = c * dH := by
  rw [hH]
  ring

/-- Applying any linear symplectic-sharp map preserves that same null-cone scaling. -/
theorem linear_sharp_respects_null_scaling
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (sharp : V →ₗ[ℝ] V) (c : ℝ) (dH : V) :
    sharp (c • dH) = c • sharp dH := by
  exact map_smul sharp c dH

/-- Hence once `dĤ=c dH` on the null cone, the corresponding Hamiltonian directions
differ only by the same positive conformal factor. -/
theorem conformal_null_hamiltonian_vector_scaling
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (sharp : V →ₗ[ℝ] V)
    (dH dHhat : V) (c : ℝ)
    (h : dHhat = c • dH) :
    sharp dHhat = c • sharp dH := by
  rw [h]
  exact map_smul sharp c dH

/-! ## 8. Relative rapidity identity -/

/-- Principal future/past null-frequency characters of the normalized optical boost. -/
def nuPlus (s : ℝ) : ℝ := Real.exp s

def nuMinus (s : ℝ) : ℝ := Real.exp (-s)

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

/-- The explicitly named optical frequencies carry the same ratio as the action characters. -/
theorem null_frequency_ratio (s : ℝ) :
    nuPlus s / nuMinus s = Real.exp (2 * s) := by
  exact master_ratio s

/-- Their normalized exchange defect is exactly the same projective coordinate. -/
theorem null_frequency_defect (s : ℝ) :
    (nuPlus s - nuMinus s) / (nuPlus s + nuMinus s) = Real.tanh s := by
  exact optical_defect_is_tanh s

/-- The action and null-frequency ratios are identically equal, with no fitted parameter. -/
theorem character_ratio_eq_null_frequency_ratio (u s : ℝ) :
    XiMUS u s / XiGUS u s = nuPlus s / nuMinus s := by
  rw [character_ratio_eq_exp_two, null_frequency_ratio]

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

/-- The paper's full relative-rest statement: sector equality, null-frequency equality,
and vanishing relational velocity are exactly the same condition. -/
theorem full_relative_rest_equivalence (u s : ℝ) :
    (XiGUS u s = XiMUS u s) ↔
      (nuPlus s = nuMinus s ∧ Real.tanh s = 0) := by
  rw [character_rest_iff_zero]
  constructor
  · intro hs
    subst s
    simp [nuPlus, nuMinus]
  · rintro ⟨hnu, hv⟩
    exact (optical_rest_iff_zero s).mp hv


/-! ### Forced action-to-optical intertwiner -/

/-- Optical even basis covector. -/
def TO : R2 := (1, 0)

/-- Optical odd basis covector. -/
def RO : R2 := (0, 1)


/-- Principal endpoint covectors obtained from the normalized null pair. -/
def principalThetaPlus : R2 := TO + RO
def principalThetaMinus : R2 := TO - RO


/-- Normalized optical Minkowski bilinear form on the time/radial covector plane. -/
def opticalBilinear : R2 →ₗ[ℝ] R2 →ₗ[ℝ] ℝ where
  toFun v :=
    { toFun := fun w => -v.1 * w.1 + v.2 * w.2
      map_add' := by
        intro x y
        simp
        ring
      map_smul' := by
        intro c x
        simp
        ring }
  map_add' := by
    intro x y
    ext w
    simp
    ring
  map_smul' := by
    intro c x
    ext w
    simp
    ring

/-- The normalized chronometric covector is unit timelike. -/
@[simp] theorem opticalBilinear_TO :
    opticalBilinear TO TO = -1 := by
  norm_num [opticalBilinear, TO]

/-- The normalized radial covector is unit spacelike. -/
@[simp] theorem opticalBilinear_RO :
    opticalBilinear RO RO = 1 := by
  norm_num [opticalBilinear, RO]

/-- Time and radial covectors are orthogonal. -/
@[simp] theorem opticalBilinear_TO_RO :
    opticalBilinear TO RO = 0 := by
  norm_num [opticalBilinear, TO, RO]

/-- The two principal endpoint covectors are exactly null. -/
theorem principal_endpoint_covectors_null :
    opticalBilinear principalThetaPlus principalThetaPlus = 0 ∧
    opticalBilinear principalThetaMinus principalThetaMinus = 0 := by
  constructor <;> norm_num
    [opticalBilinear, principalThetaPlus, principalThetaMinus, TO, RO]

/-- Half-sum and half-difference of the principal null endpoints recover exactly the
chronometric and radial covectors. -/
theorem principal_endpoint_split :
    (1 / 2 : ℝ) • (principalThetaPlus + principalThetaMinus) = TO ∧
    (1 / 2 : ℝ) • (principalThetaPlus - principalThetaMinus) = RO := by
  constructor <;> ext <;>
    norm_num [principalThetaPlus, principalThetaMinus, TO, RO]

/-- The principal radial covector is genuinely nonzero. -/
theorem RO_ne_zero : RO ≠ 0 := by
  intro h
  have h2 := congrArg Prod.snd h
  norm_num [RO] at h2


/-- Optical exchange fixes the clock-even axis and reverses the radial-odd axis. -/
def JO (v : R2) : R2 := (v.1, -v.2)

@[simp] theorem JO_TO : JO TO = TO := by
  ext <;> norm_num [JO, TO]

@[simp] theorem JO_RO : JO RO = -RO := by
  ext <;> norm_num [JO, RO]

@[simp] theorem JO_sq (v : R2) : JO (JO v) = v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [JO]

/-- Evaluation pairing for the finite-dimensional optical model. -/
def opticalEval (α v : R2) : ℝ := α.1 * v.1 + α.2 * v.2

/-- Unit boosted observer in the normalized optical basis. -/
def opticalObserver (s : ℝ) : R2 := (Real.cosh s, Real.sinh s)

/-- The operational radial/time ratio of the boosted observer is exactly `tanh s`. -/
theorem optical_velocity_ratio (s : ℝ) :
    opticalEval RO (opticalObserver s) / opticalEval TO (opticalObserver s) =
      Real.tanh s := by
  simp [opticalEval, RO, TO, opticalObserver, Real.tanh_eq_sinh_div_cosh]

/-- The manuscript's operational defect-velocity equation is an identity:
the optical radial/time ratio and the action odd/even ratio are the same `tanh s`. -/
theorem defectvelocity_identity
    (η s : ℝ) (hη : η ≠ 0) :
    opticalEval RO (opticalObserver s) / opticalEval TO (opticalObserver s) =
      - carrierOdd η s / carrierEven η s := by
  rw [optical_velocity_ratio s, carrier_ratio η s hη]

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

/-- The normalized action-to-optical identification intertwines exchange exactly. -/
theorem actionOpticalMap_intertwines_exchange (v : R2) :
    actionOpticalMap (JA v) = JO (actionOpticalMap v) := by
  rcases v with ⟨x, y⟩
  ext <;> simp [actionOpticalMap, JA, JO] <;> ring

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


/-- The optical boosts obey the same additive rapidity group law. -/
theorem opticalBoost_add (s t : ℝ) (v : R2) :
    opticalBoost (s + t) v = opticalBoost s (opticalBoost t v) := by
  rcases v with ⟨x, y⟩
  ext <;>
    simp [opticalBoost, Real.cosh_add, Real.sinh_add] <;>
    ring

/-- Negative rapidity is the inverse optical boost. -/
theorem opticalBoost_neg_inverse (s : ℝ) (v : R2) :
    opticalBoost (-s) (opticalBoost s v) = v := by
  rw [← opticalBoost_add]
  simp [opticalBoost]

/-- Optical exchange reverses rapidity exactly as action-sector exchange does. -/
theorem JO_opticalBoost (s : ℝ) (v : R2) :
    JO (opticalBoost s v) = opticalBoost (-s) (JO v) := by
  rcases v with ⟨x, y⟩
  ext <;> simp [JO, opticalBoost, Real.cosh_neg, Real.sinh_neg] <;> ring

@[simp] theorem opticalBoost_zero (v : R2) : opticalBoost 0 v = v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [opticalBoost]

/-- The first optical component obeys the normalized boost-generator equation. -/
theorem opticalBoost_fst_hasDerivAt (v : R2) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (opticalBoost t v).1)
      (BO (opticalBoost s v)).1 s := by
  rcases v with ⟨x, y⟩
  have hfirst :=
    (Real.hasDerivAt_cosh s).mul_const x |>.add
      ((Real.hasDerivAt_sinh s).mul_const y)
  simpa [opticalBoost, BO, mul_comm, mul_left_comm, mul_assoc] using hfirst

/-- The second optical component obeys the normalized boost-generator equation. -/
theorem opticalBoost_snd_hasDerivAt (v : R2) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (opticalBoost t v).2)
      (BO (opticalBoost s v)).2 s := by
  rcases v with ⟨x, y⟩
  have hsecond :=
    (Real.hasDerivAt_sinh s).mul_const x |>.add
      ((Real.hasDerivAt_cosh s).mul_const y)
  simpa [opticalBoost, BO, mul_comm, mul_left_comm, mul_assoc] using hsecond

/-- Componentwise, the finite optical boost is exactly the integral curve of `BO`. -/
theorem opticalBoost_generated_by_BO (v : R2) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (opticalBoost t v).1)
        (BO (opticalBoost s v)).1 s ∧
    HasDerivAt (fun t : ℝ => (opticalBoost t v).2)
        (BO (opticalBoost s v)).2 s :=
  ⟨opticalBoost_fst_hasDerivAt v s, opticalBoost_snd_hasDerivAt v s⟩

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


/-- The normalized action-to-optical map is injective. -/
theorem actionOpticalMap_injective : Function.Injective actionOpticalMap := by
  intro x y h
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp [actionOpticalMap] at h₁ h₂
  ext <;> linarith

/-- The normalized action-to-optical map is surjective. -/
theorem actionOpticalMap_surjective : Function.Surjective actionOpticalMap := by
  rintro ⟨t, r⟩
  refine ⟨(t - r, t + r), ?_⟩
  ext <;> simp [actionOpticalMap] <;> ring

/-- Equality of normalized boosted optical time directions forces equality of rapidities. -/
theorem opticalBoost_TO_injective :
    Function.Injective (fun s : ℝ => opticalBoost s TO) := by
  intro σ s h
  have hc := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  simp [opticalBoost, TO] at hc hs
  have he : Real.exp σ = Real.exp s := by
    rw [← Real.cosh_add_sinh σ, ← Real.cosh_add_sinh s, hc, hs]
  exact Real.exp_injective he

/-- Once the normalized action and optical boost representations are intertwined,
the optical rapidity is not a free reparametrization: it is exactly the action coordinate. -/
theorem rapidity_forced_by_normalized_boost
    (s σ : ℝ)
    (h : opticalBoost σ TO = actionOpticalMap (actionBoost s CA)) :
    σ = s := by
  have hi := actionOpticalMap_intertwines_boost s CA
  rw [actionOpticalMap_CA] at hi
  apply opticalBoost_TO_injective
  exact h.trans hi

/-! ## 9. Abstract Iyer–Wald/characteristic linear descent

The physics-specific derivation of the Iyer–Wald current is deliberately not assumed globally.
Instead, this section proves the *forced linear algebra* once a parameter-to-characteristic map
and its stress response are supplied.  These theorems are directly reusable when the full
Einstein–Maxwell current is formalized.
-/

/-! ### Boundary-compensated Iyer-Wald sign algebra -/

/-- Common-character-removed relative constraint residual when the gravity and Maxwell
constraint contributions agree at the fixed point. -/
def relativeConstraintResidual (ell s : ℝ) : ℝ :=
  Real.exp (-s) * (ell - Real.exp (2 * s) * ell)

/-- Reciprocal relative scaling forces the constraint residual to be the same odd sinh carrier. -/
theorem relativeConstraintResidual_eq_sinh (ell s : ℝ) :
    relativeConstraintResidual ell s = -2 * Real.sinh s * ell := by
  unfold relativeConstraintResidual
  have hexp : Real.exp (-s) * Real.exp (2 * s) = Real.exp s := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-s) * (ell - Real.exp (2 * s) * ell)
        = ell * (Real.exp (-s) - Real.exp (-s) * Real.exp (2 * s)) := by ring
    _ = ell * (Real.exp (-s) - Real.exp s) := by rw [hexp]
    _ = -2 * Real.sinh s * ell := by
      rw [Real.sinh_eq]
      ring

/-- Its fixed-point normal derivative is forced to be exactly `-2 ell`. -/
theorem relativeConstraintResidual_hasDerivAt_zero (ell : ℝ) :
    HasDerivAt (relativeConstraintResidual ell) (-2 * ell) 0 := by
  have hfun :
      relativeConstraintResidual ell =
        fun s : ℝ => (-2 * ell) * Real.sinh s := by
    funext s
    rw [relativeConstraintResidual_eq_sinh]
    ring
  rw [hfun]
  simpa using (Real.hasDerivAt_sinh 0).const_mul (-2 * ell)

/-- Therefore the relative constraint variation appearing in the Iyer-Wald identity
is not an independent coefficient. -/
theorem relativeConstraintResidual_deriv_zero (ell : ℝ) :
    deriv (relativeConstraintResidual ell) 0 = -2 * ell :=
  (relativeConstraintResidual_hasDerivAt_zero ell).deriv

/-- Antisymmetry plus the off-shell Iyer-Wald identity forces the boundary-compensated
current to equal the constraint response. -/
theorem iyerWald_boundary_compensation
    (omegaYX omegaXY dB deltaC : ℝ)
    (hanti : omegaXY = -omegaYX)
    (hIW : omegaYX = dB - deltaC) :
    omegaXY + dB = deltaC := by
  rw [hanti, hIW]
  ring

/-- With the Einstein-Maxwell relative response `δC=-2ℓ`, the compensated current is
therefore exactly the bulk stress response `-2ℓ`. -/
theorem iyerWald_bulk_response
    (omegaYX omegaXY dB deltaC ell : ℝ)
    (hanti : omegaXY = -omegaYX)
    (hIW : omegaYX = dB - deltaC)
    (hC : deltaC = -2 * ell) :
    omegaXY + dB = -2 * ell := by
  rw [iyerWald_boundary_compensation omegaYX omegaXY dB deltaC hanti hIW, hC]


/-- Stronger form: when the Iyer-Wald constraint variation is the derivative of the
reciprocally scaled constraint residual, the bulk response `-2ℓ` follows automatically. -/
theorem iyerWald_bulk_response_from_relative_scaling
    (omegaYX omegaXY dB ell : ℝ)
    (hanti : omegaXY = -omegaYX)
    (hIW :
      omegaYX =
        dB - deriv (relativeConstraintResidual ell) 0) :
    omegaXY + dB = -2 * ell := by
  have hC := relativeConstraintResidual_deriv_zero ell
  exact iyerWald_bulk_response
    omegaYX omegaXY dB
    (deriv (relativeConstraintResidual ell) 0) ell
    hanti hIW hC

/-- Consequently the characteristic half-contraction normalization is forced directly
from reciprocal sector scaling plus the off-shell Iyer-Wald identity. -/
theorem characteristic_half_contraction_from_relative_scaling
    (omegaYX omegaXY dB ell : ℝ)
    (hanti : omegaXY = -omegaYX)
    (hIW :
      omegaYX =
        dB - deriv (relativeConstraintResidual ell) 0) :
    -(1 / 2 : ℝ) * (omegaXY + dB) = ell := by
  rw [iyerWald_bulk_response_from_relative_scaling
    omegaYX omegaXY dB ell hanti hIW]
  ring

/-- The manuscript's characteristic covector sign is then forced algebraically. -/
theorem characteristic_half_contraction
    (OmegaXY ell : ℝ)
    (hOmega : OmegaXY = -2 * ell) :
    -(1 / 2 : ℝ) * OmegaXY = ell := by
  rw [hOmega]
  ring

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

/-- When the characteristic space is literally `im β`, uniqueness of the descended
covector needs no separately supplied surjectivity hypothesis. -/
theorem characteristic_range_covector_unique
    (β : P →ₗ[ℝ] K)
    (ℓ : P →ₗ[ℝ] ℝ)
    (Λ₁ Λ₂ : LinearMap.range β →ₗ[ℝ] ℝ)
    (h₁ : Λ₁.comp β.rangeRestrict = ℓ)
    (h₂ : Λ₂.comp β.rangeRestrict = ℓ) :
    Λ₁ = Λ₂ := by
  exact covector_pullback_injective β.rangeRestrict
    (LinearMap.surjective_rangeRestrict β) (h₁.trans h₂.symm)

/-- A covector with a prescribed pullback is unique. -/
theorem descended_covector_unique
    (β : P →ₗ[ℝ] K) (hβ : Function.Surjective β)
    (ℓ : P →ₗ[ℝ] ℝ) (Λ₁ Λ₂ : K →ₗ[ℝ] ℝ)
    (h₁ : Λ₁.comp β = ℓ) (h₂ : Λ₂.comp β = ℓ) :
    Λ₁ = Λ₂ := by
  apply covector_pullback_injective β hβ
  exact h₁.trans h₂.symm


/-- If the physical response vanishes on every parameter invisible to the characteristic map,
then the characteristic covector is not merely unique: it exists canonically on `im β`. -/
noncomputable def characteristicCovectorOfKernel
    (β : P →ₗ[ℝ] K) (ℓ : P →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker β ≤ LinearMap.ker ℓ) :
    LinearMap.range β →ₗ[ℝ] ℝ :=
  ((LinearMap.ker β).liftQ ℓ hker).comp
    (LinearMap.quotKerEquivRange β).symm.toLinearMap

/-- The canonical covector constructed from kernel-invisibility pulls back to the original
physical response exactly. -/
theorem characteristicCovectorOfKernel_factorization
    (β : P →ₗ[ℝ] K) (ℓ : P →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker β ≤ LinearMap.ker ℓ) :
    (characteristicCovectorOfKernel β ℓ hker).comp β.rangeRestrict = ℓ := by
  ext p
  simp [characteristicCovectorOfKernel]

/-- Kernel-invisibility therefore forces a unique covector on the actual characteristic image. -/
theorem characteristicCovectorOfKernel_unique
    (β : P →ₗ[ℝ] K) (ℓ : P →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker β ≤ LinearMap.ker ℓ)
    (Λ : LinearMap.range β →ₗ[ℝ] ℝ)
    (hΛ : Λ.comp β.rangeRestrict = ℓ) :
    Λ = characteristicCovectorOfKernel β ℓ hker := by
  exact characteristic_range_covector_unique β ℓ Λ
    (characteristicCovectorOfKernel β ℓ hker)
    hΛ (characteristicCovectorOfKernel_factorization β ℓ hker)

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


/-- If the integrated response depends only on the characteristic variation, kernel invisibility
is itself forced rather than assumed. -/
theorem kernel_invisible_of_response_extensional
    (β : P →ₗ[ℝ] K) (ℓ : P →ₗ[ℝ] ℝ)
    (hext : ∀ p q : P, β p = β q → ℓ p = ℓ q) :
    LinearMap.ker β ≤ LinearMap.ker ℓ := by
  intro p hp
  change ℓ p = 0
  have h := hext p 0
  simp [hp] at h
  exact h

/-- When the characteristic space is defined, as in the manuscript, to be the image of
the parameter-to-characteristic map, surjectivity is automatic rather than an extra hypothesis. -/
theorem characteristic_range_restriction_surjective
    (β : P →ₗ[ℝ] K) :
    Function.Surjective β.rangeRestrict :=
  LinearMap.surjective_rangeRestrict β

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

/-- The clock covector on the quotient is constructed canonically by quotienting out
exactly the directions it annihilates. -/
noncomputable def quotientClockCovector
    (Λ : K →ₗ[ℝ] ℝ) :
    (K ⧸ LinearMap.ker Λ) →ₗ[ℝ] ℝ :=
  (LinearMap.ker Λ).liftQ Λ le_rfl

/-- Its pullback along the quotient projection is exactly the original characteristic covector. -/
theorem quotientClockCovector_pullback
    (Λ : K →ₗ[ℝ] ℝ) :
    (quotientClockCovector Λ).comp (LinearMap.ker Λ).mkQ = Λ := by
  simpa [quotientClockCovector] using
    (Submodule.liftQ_mkQ (LinearMap.ker Λ) Λ le_rfl)

/-- Quotienting by the full kernel leaves no further invisible clock direction. -/
theorem quotientClockCovector_ker_eq_bot
    (Λ : K →ₗ[ℝ] ℝ) :
    LinearMap.ker (quotientClockCovector Λ) = ⊥ := by
  simpa [quotientClockCovector] using
    (Submodule.ker_liftQ_eq_bot'
      (LinearMap.ker Λ) Λ rfl)

/-- Hence the descended clock covector is injective. -/
theorem quotientClockCovector_injective
    (Λ : K →ₗ[ℝ] ℝ) :
    Function.Injective (quotientClockCovector Λ) := by
  rw [← LinearMap.ker_eq_bot]
  exact quotientClockCovector_ker_eq_bot Λ

/-- If the original response is nonzero, the quotient clock covector is also nonzero. -/
theorem quotientClockCovector_nonzero
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    quotientClockCovector Λ ≠ 0 := by
  intro hzero
  apply hΛ
  rw [← quotientClockCovector_pullback Λ, hzero]
  simp

/-- For a nonzero response, the quotient clock covector is surjective onto the real line. -/
theorem quotientClockCovector_surjective
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    Function.Surjective (quotientClockCovector Λ) :=
  LinearMap.surjective (quotientClockCovector_nonzero Λ hΛ)

/-- The quotient clock covector is therefore itself the canonical linear equivalence with ℝ. -/
noncomputable def quotientClockCovectorEquivReal
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    (K ⧸ LinearMap.ker Λ) ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective (quotientClockCovector Λ)
    ⟨quotientClockCovector_injective Λ,
      quotientClockCovector_surjective Λ hΛ⟩

/-- The quotient by the kernel of a nonzero real covector is canonically equivalent to its range. -/
noncomputable def clockQuotientEquivRange (Λ : K →ₗ[ℝ] ℝ) :
    (K ⧸ LinearMap.ker Λ) ≃ₗ[ℝ] LinearMap.range Λ :=
  LinearMap.quotKerEquivRange Λ

/-- A nonzero clock covector makes its kernel quotient canonically equivalent to `ℝ`. -/
noncomputable def clockQuotientEquivReal
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    (K ⧸ LinearMap.ker Λ) ≃ₗ[ℝ] ℝ :=
  (LinearMap.quotKerEquivRange Λ).trans
    ((LinearEquiv.ofEq (LinearMap.range Λ) ⊤
      (LinearMap.range_eq_top.mpr (LinearMap.surjective hΛ))).trans
      Submodule.topEquiv)

/-- Therefore the stress-visible quotient has exactly one real dimension. -/
theorem clockQuotient_finrank_one
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    Module.finrank ℝ (K ⧸ LinearMap.ker Λ) = 1 := by
  calc
    Module.finrank ℝ (K ⧸ LinearMap.ker Λ)
        = Module.finrank ℝ ℝ := LinearEquiv.finrank_eq (clockQuotientEquivReal Λ hΛ)
    _ = 1 := CommSemiring.finrank_self ℝ

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

/-- In particular, every clock one-form with the required pullback is the canonical quotient lift. -/
theorem quotient_clock_covector_forced
    (Λ : K →ₗ[ℝ] ℝ)
    (λ : (K ⧸ LinearMap.ker Λ) →ₗ[ℝ] ℝ)
    (hλ : λ.comp (LinearMap.ker Λ).mkQ = Λ) :
    λ = quotientClockCovector Λ := by
  exact quotient_clock_covector_unique Λ λ (quotientClockCovector Λ)
    hλ (quotientClockCovector_pullback Λ)

end LinearDescent

/-! ### Bilinear/presymplectic descent through a characteristic quotient -/

section BilinearDescent

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- If a bilinear form annihilates a characteristic subspace in both slots, it descends
canonically to the quotient. -/
def quotientBilinearForm
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (p : Submodule ℝ V)
    (hleft : p ≤ LinearMap.ker B)
    (hright : p ≤ LinearMap.ker B.flip) :
    (V ⧸ p) →ₗ[ℝ] (V ⧸ p) →ₗ[ℝ] ℝ :=
  B.liftQ₂ p p hleft hright

/-- Pulling the descended form back to representatives recovers the original form exactly. -/
@[simp] theorem quotientBilinearForm_mk
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (p : Submodule ℝ V)
    (hleft : p ≤ LinearMap.ker B)
    (hright : p ≤ LinearMap.ker B.flip)
    (x y : V) :
    quotientBilinearForm B p hleft hright
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      B x y := by
  rfl

/-- A bilinear form on the quotient is uniquely determined by its pullback on representatives. -/
theorem quotientBilinearForm_unique
    (p : Submodule ℝ V)
    (B₁ B₂ : (V ⧸ p) →ₗ[ℝ] (V ⧸ p) →ₗ[ℝ] ℝ)
    (h :
      ∀ x y : V,
        B₁ (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
          B₂ (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)) :
    B₁ = B₂ := by
  ext x y
  refine Submodule.Quotient.induction_on _ x ?_
  intro vx
  refine Submodule.Quotient.induction_on _ y ?_
  intro vy
  exact h vx vy

/-- Skew-symmetry survives characteristic descent. -/
theorem quotientBilinearForm_skew
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (p : Submodule ℝ V)
    (hleft : p ≤ LinearMap.ker B)
    (hright : p ≤ LinearMap.ker B.flip)
    (hskew : ∀ x y : V, B x y = - B y x) :
    ∀ x y : V ⧸ p,
      quotientBilinearForm B p hleft hright x y =
        - quotientBilinearForm B p hleft hright y x := by
  intro x y
  refine Submodule.Quotient.induction_on x ?_
  intro vx
  refine Submodule.Quotient.induction_on y ?_
  intro vy
  simpa using hskew vx vy

/-- If a skew form annihilates the characteristic subspace in the first slot, the second
radical condition is automatic. -/
theorem skew_right_radical_of_left
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (p : Submodule ℝ V)
    (hskew : ∀ x y : V, B x y = - B y x)
    (hleft : p ≤ LinearMap.ker B) :
    p ≤ LinearMap.ker B.flip := by
  intro z hz
  apply LinearMap.ext
  intro x
  have hz0 : B z x = 0 := by
    have hzker := hleft hz
    change B z = 0 at hzker
    exact LinearMap.congr_fun hzker x
  simp [LinearMap.flip_apply, hskew x z, hz0]

/-- Hence a skew presymplectic form descends as soon as the characteristic directions
lie in its kernel. -/
def skewQuotientBilinearForm
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (p : Submodule ℝ V)
    (hskew : ∀ x y : V, B x y = - B y x)
    (hchar : p ≤ LinearMap.ker B) :
    (V ⧸ p) →ₗ[ℝ] (V ⧸ p) →ₗ[ℝ] ℝ :=
  quotientBilinearForm B p hchar
    (skew_right_radical_of_left B p hskew hchar)

end BilinearDescent

/-! ## 10. One-dimensional covector-preserving identification -/

section OneDimensional

variable {L₁ L₂ : Type*}
  [AddCommGroup L₁] [Module ℝ L₁]
  [AddCommGroup L₂] [Module ℝ L₂]

/-- In a genuinely one-dimensional real vector space, a normalized covector and its
unit vector force the reconstruction formula; it is not an additional hypothesis. -/
theorem reconstruction_from_normalized_covector
    (α : L₁ →ₗ[ℝ] ℝ) (u : L₁)
    (hu : α u = 1)
    (hfin : Module.finrank ℝ L₁ = 1) :
    ∀ x : L₁, x = (α x) • u := by
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero] at hu
    simp at hu
  intro x
  rcases ((finrank_eq_one_iff_of_nonzero' u hu0).mp hfin x) with ⟨c, hc⟩
  have hcoeff : c = α x := by
    have hx := congrArg α hc
    simpa [hu] using hx
  calc
    x = c • u := hc.symm
    _ = (α x) • u := by rw [hcoeff]

/-- In a one-dimensional source, the image of its normalized unit determines a linear map uniquely. -/
theorem unique_covector_preserving_map
    (α : L₁ →ₗ[ℝ] ℝ)
    (u₁ : L₁) (u₂ : L₂)
    (hαu : α u₁ = 1)
    (hfin₁ : Module.finrank ℝ L₁ = 1)
    (I J : L₁ →ₗ[ℝ] L₂)
    (hIu : I u₁ = u₂) (hJu : J u₁ = u₂) : I = J := by
  have hspan₁ := reconstruction_from_normalized_covector α u₁ hαu hfin₁
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


/-- On a one-dimensional real clock line, a nonzero covector selects exactly one normalized unit. -/
theorem normalized_unit_existsUnique
    (α : L₁ →ₗ[ℝ] ℝ)
    (hα : α ≠ 0)
    (hfin : Module.finrank ℝ L₁ = 1) :
    ∃! u : L₁, α u = 1 := by
  obtain ⟨u, hu⟩ := (LinearMap.surjective hα) 1
  refine ⟨u, hu, ?_⟩
  intro v hv
  have hspan := reconstruction_from_normalized_covector α u hu hfin
  exact normalized_unit_unique α u v hu hspan hv


/-- Canonical normalized direction selected by a nonzero covector on a one-dimensional line. -/
noncomputable def normalizedClockUnit
    (α : L₁ →ₗ[ℝ] ℝ)
    (hα : α ≠ 0)
    (hfin : Module.finrank ℝ L₁ = 1) : L₁ :=
  Classical.choose (normalized_unit_existsUnique α hα hfin)

@[simp] theorem normalizedClockUnit_eval
    (α : L₁ →ₗ[ℝ] ℝ)
    (hα : α ≠ 0)
    (hfin : Module.finrank ℝ L₁ = 1) :
    α (normalizedClockUnit α hα hfin) = 1 :=
  (Classical.choose_spec (normalized_unit_existsUnique α hα hfin)).1

/-- On the descended one-dimensional contact line the Reeb normalization has one and only
one possible direction.  Closedness is automatic from one-dimensionality above. -/
theorem reeb_direction_unique
    (α : L₁ →ₗ[ℝ] ℝ)
    (hα : α ≠ 0)
    (hfin : Module.finrank ℝ L₁ = 1)
    (R : L₁) (hR : α R = 1) :
    R = normalizedClockUnit α hα hfin := by
  exact (Classical.choose_spec
    (normalized_unit_existsUnique α hα hfin)).2 R hR


/-- Every alternating bilinear two-form vanishes on a one-dimensional clock line.
This is the algebraic content of the manuscript's statement that the descended one-form is closed. -/
theorem alternating_bilinear_zero_on_clock_line
    (α : L₁ →ₗ[ℝ] ℝ) (u : L₁)
    (hu : α u = 1)
    (hfin : Module.finrank ℝ L₁ = 1)
    (B : L₁ →ₗ[ℝ] L₁ →ₗ[ℝ] ℝ)
    (halt : ∀ x : L₁, B x x = 0) :
    ∀ x y : L₁, B x y = 0 := by
  have hspan := reconstruction_from_normalized_covector α u hu hfin
  intro x y
  rw [hspan x, hspan y]
  simp [halt u]

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

/-- On a one-dimensional target line, covector preservation alone forces the canonical map. -/
theorem normalizedClockMap_unique_of_covector
    (α : L₁ →ₗ[ℝ] ℝ) (β : L₂ →ₗ[ℝ] ℝ) (u₂ : L₂)
    (hβu : β u₂ = 1)
    (hfin₂ : Module.finrank ℝ L₂ = 1)
    (I : L₁ →ₗ[ℝ] L₂)
    (hpres : β.comp I = α) :
    I = normalizedClockMap α u₂ := by
  have hspan₂ := reconstruction_from_normalized_covector β u₂ hβu hfin₂
  ext x
  rw [hspan₂ (I x)]
  have hx := LinearMap.congr_fun hpres x
  change β (I x) = α x at hx
  rw [hx]
  rfl

/-- Between two one-dimensional normalized clock lines, the canonical covector-preserving
map is automatically bijective. -/
theorem normalizedClockMap_bijective
    (α : L₁ →ₗ[ℝ] ℝ) (β : L₂ →ₗ[ℝ] ℝ)
    (u₁ : L₁) (u₂ : L₂)
    (hαu : α u₁ = 1) (hβu : β u₂ = 1)
    (hfin₁ : Module.finrank ℝ L₁ = 1)
    (hfin₂ : Module.finrank ℝ L₂ = 1) :
    Function.Bijective (normalizedClockMap α u₂) := by
  have hspan₁ := reconstruction_from_normalized_covector α u₁ hαu hfin₁
  have hspan₂ := reconstruction_from_normalized_covector β u₂ hβu hfin₂
  constructor
  · intro x y hxy
    have hb := congrArg β hxy
    simp [normalizedClockMap, hβu] at hb
    rw [hspan₁ x, hspan₁ y, hb]
  · intro y
    refine ⟨(β y) • u₁, ?_⟩
    rw [normalizedClockMap_apply, map_smul, hαu, smul_eq_mul, mul_one]
    exact (hspan₂ y).symm

/-- Hence the global/local clock identification is a genuine linear equivalence once both
descended covectors have fixed their normalized units. -/
noncomputable def normalizedClockEquiv
    (α : L₁ →ₗ[ℝ] ℝ) (β : L₂ →ₗ[ℝ] ℝ)
    (u₁ : L₁) (u₂ : L₂)
    (hαu : α u₁ = 1) (hβu : β u₂ = 1)
    (hfin₁ : Module.finrank ℝ L₁ = 1)
    (hfin₂ : Module.finrank ℝ L₂ = 1) :
    L₁ ≃ₗ[ℝ] L₂ :=
  LinearEquiv.ofBijective (normalizedClockMap α u₂)
    (normalizedClockMap_bijective α β u₁ u₂ hαu hβu hfin₁ hfin₂)

/-- Scalar multiplication of a distinguished covector defines the natural map from the
relative normal line into the dual of a one-dimensional clock line. -/
def covectorScaleMap
    (α : L₁ →ₗ[ℝ] ℝ) :
    ℝ →ₗ[ℝ] (L₁ →ₗ[ℝ] ℝ) where
  toFun c := c • α
  map_add' a b := by
    ext x
    simp [add_smul]
  map_smul' c a := by
    ext x
    simp [mul_smul]

/-- On a one-dimensional clock line, every covector is a unique scalar multiple of any
chosen nonzero normalized clock covector. -/
theorem covectorScaleMap_bijective
    (α : L₁ →ₗ[ℝ] ℝ)
    (hα : α ≠ 0)
    (hfin : Module.finrank ℝ L₁ = 1) :
    Function.Bijective (covectorScaleMap α) := by
  let u := normalizedClockUnit α hα hfin
  have hu : α u = 1 := normalizedClockUnit_eval α hα hfin
  have hspan := reconstruction_from_normalized_covector α u hu hfin
  constructor
  · intro a b hab
    have hfun := LinearMap.congr_fun hab u
    simp [covectorScaleMap, hu] at hfun
    exact hfun
  · intro β
    refine ⟨β u, ?_⟩
    ext x
    rw [hspan x]
    simp [covectorScaleMap, hu, mul_comm]

/-- The relative scalar normal line is canonically equivalent to the dual of the
one-dimensional descended clock line. -/
noncomputable def normalizedCovectorDualEquiv
    (α : L₁ →ₗ[ℝ] ℝ)
    (hα : α ≠ 0)
    (hfin : Module.finrank ℝ L₁ = 1) :
    ℝ ≃ₗ[ℝ] (L₁ →ₗ[ℝ] ℝ) :=
  LinearEquiv.ofBijective (covectorScaleMap α)
    (covectorScaleMap_bijective α hα hfin)

end OneDimensional

/-! ### Contact-transverse duality for the characteristic quotient -/

section ClockQuotientDuality

variable {K : Type*} [AddCommGroup K] [Module ℝ K]

/-- Exact algebraic form of the manuscript's contact-transverse duality:
the one-dimensional relative normal line is canonically the dual of the stress-visible
characteristic quotient. -/
noncomputable def clockQuotientDualEquiv
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    ℝ ≃ₗ[ℝ] ((K ⧸ LinearMap.ker Λ) →ₗ[ℝ] ℝ) :=
  normalizedCovectorDualEquiv
    (quotientClockCovector Λ)
    (quotientClockCovector_nonzero Λ hΛ)
    (clockQuotient_finrank_one Λ hΛ)

end ClockQuotientDuality

/-! ### Exact affine primitive of the descended clock covector -/

section AffineClockPrimitive

variable {L : Type*} [AddCommGroup L] [Module ℝ L]

/-- A descended linear clock covector has an explicit affine primitive. -/
def clockPotential (λ : L →ₗ[ℝ] ℝ) (C : ℝ) (x : L) : ℝ :=
  λ x + C

/-- Its increment is exactly the clock covector, globally on the quotient vector space. -/
theorem clockPotential_increment
    (λ : L →ₗ[ℝ] ℝ) (C : ℝ) (x v : L) :
    clockPotential λ C (x + v) - clockPotential λ C x = λ v := by
  simp [clockPotential]
  ring

/-- Changing the integration constant changes only the clock origin. -/
theorem clockPotential_origin_shift
    (λ : L →ₗ[ℝ] ℝ) (C₁ C₂ : ℝ) (x : L) :
    clockPotential λ C₂ x - clockPotential λ C₁ x = C₂ - C₁ := by
  simp [clockPotential]
  ring

/-- Any two functions with the same translation differential differ by one global constant.
This is the precise affine version of `[Θ] ∈ C∞(L)/ℝ` on the linear clock quotient. -/
theorem clockPotential_unique_up_to_constant
    (λ : L →ₗ[ℝ] ℝ) (Θ₁ Θ₂ : L → ℝ)
    (h₁ : ∀ x v : L, Θ₁ (x + v) - Θ₁ x = λ v)
    (h₂ : ∀ x v : L, Θ₂ (x + v) - Θ₂ x = λ v) :
    ∀ x : L, Θ₁ x - Θ₂ x = Θ₁ 0 - Θ₂ 0 := by
  intro x
  have h1 := h₁ 0 x
  have h2 := h₂ 0 x
  simp at h1 h2
  linarith

/-- Along a normalized unit direction, the affine clock advances by exactly the parameter. -/
theorem clockPotential_normalized_flow
    (λ : L →ₗ[ℝ] ℝ) (u : L) (hu : λ u = 1)
    (C t : ℝ) (x : L) :
    clockPotential λ C (x + t • u) = clockPotential λ C x + t := by
  simp [clockPotential, hu]
  ring

/-- Any two clock representatives normalized by the same flow differ by a first integral
of that flow.  This is the torsor statement used before null synchronization. -/
theorem clock_representatives_differ_by_first_integral
    {X : Type*}
    (flow : ℝ → X → X)
    (Θ₁ Θ₂ : X → ℝ)
    (h₁ : ∀ t x, Θ₁ (flow t x) = Θ₁ x + t)
    (h₂ : ∀ t x, Θ₂ (flow t x) = Θ₂ x + t) :
    ∀ t x, Θ₁ (flow t x) - Θ₂ (flow t x) = Θ₁ x - Θ₂ x := by
  intro t x
  rw [h₁ t x, h₂ t x]
  ring

end AffineClockPrimitive

/-! ## 11. Pointwise local clock algebra -/

/-- Scalar algebra behind the symmetric-carrier decomposition
`Jv = ω T_O(v) u_* + w`: self-adjointness fixes the coefficient. -/
theorem carrier_decomposition_coefficient
    (a g χ ω TOv : ℝ)
    (hself : -a = χ * g)
    (hTO : TOv = -ω * g)
    (hχ : χ = ω^2) :
    a = ω * TOv := by
  rw [hTO, hχ] at hself ⊢
  nlinarith

/-- A nonzero pointwise response scale makes the local ratio coefficient unique and equal
to the chronometric covector value. -/
theorem local_response_ratio_forces_clock
    (c TOv λ : ℝ) (hc : c ≠ 0)
    (hresponse : c * TOv = λ * c) :
    λ = TOv := by
  apply mul_right_cancel₀ hc
  simpa [mul_comm] using hresponse.symm


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

/-- Normalization on the distinguished unit forces the local clock covector to be nonzero. -/
theorem localClock_lambda_nonzero (D : LocalClockData (V:=V)) :
    D.lambda ≠ 0 := by
  intro hzero
  have h := D.normalized
  rw [hzero] at h
  simp at h

/-- The local stress-visible quotient is canonically a real line. -/
noncomputable def localClockQuotientEquivReal
    (D : LocalClockData (V:=V)) :
    (V ⧸ LinearMap.ker D.lambda) ≃ₗ[ℝ] ℝ :=
  clockQuotientEquivReal D.lambda (localClock_lambda_nonzero D)

/-- Consequently the local quotient has exactly one real dimension. -/
theorem localClockQuotient_finrank_one
    (D : LocalClockData (V:=V)) :
    Module.finrank ℝ (V ⧸ LinearMap.ker D.lambda) = 1 := by
  exact clockQuotient_finrank_one D.lambda (localClock_lambda_nonzero D)

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

/-- Scalar model of the future-oriented Maxwell response used to prove that the
characteristic clock covector cannot vanish. -/
def maxwellPositiveResponse (f χ vol : ℝ) : ℝ :=
  f * χ * vol / (16 * Real.pi)

/-- Maxwell positivity forces a strictly positive response whenever the smearing,
carrier magnitude, and oriented hypersurface density are positive. -/
theorem maxwellPositiveResponse_pos
    (f χ vol : ℝ)
    (hf : 0 < f) (hχ : 0 < χ) (hvol : 0 < vol) :
    0 < maxwellPositiveResponse f χ vol := by
  unfold maxwellPositiveResponse
  positivity

/-- Hence the positivity witness used in characteristic descent is not a normalization choice:
any positive nonzero Maxwell test profile supplies one. -/
theorem maxwellPositiveResponse_ne_zero
    (f χ vol : ℝ)
    (hf : 0 < f) (hχ : 0 < χ) (hvol : 0 < vol) :
    maxwellPositiveResponse f χ vol ≠ 0 :=
  ne_of_gt (maxwellPositiveResponse_pos f χ vol hf hχ hvol)

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

/-- Positivity upgrades `ω²=16π ε` to the manuscript's normalized rate
`ω=4√(π ε)`. -/
theorem energy_density_clock_rate_value
    (ε ω : ℝ)
    (hε : 0 ≤ ε) (hω : 0 ≤ ω)
    (hsq : ω^2 = 16 * Real.pi * ε) :
    ω = 4 * Real.sqrt (Real.pi * ε) := by
  have hpie : 0 ≤ Real.pi * ε :=
    mul_nonneg (le_of_lt Real.pi_pos) hε
  have hsqrt : (Real.sqrt (Real.pi * ε))^2 = Real.pi * ε :=
    Real.sq_sqrt hpie
  have hrhs : 0 ≤ 4 * Real.sqrt (Real.pi * ε) := by positivity
  nlinarith

/-- The electromagnetic clock identities close into one forced scalar chain:
the same positive `ω` is fixed by energy density and its fourth power is the invariant
Maxwell magnitude. -/
theorem chronometric_invariant_chain
    (E B ε ω : ℝ)
    (hε : 0 ≤ ε) (hω : 0 ≤ ω)
    (hcarrier : ω^2 = principalChi E B)
    (henergy : principalChi E B = 16 * Real.pi * ε) :
    ω = 4 * Real.sqrt (Real.pi * ε) ∧
    ω^4 = (maxwellI E B)^2 + (maxwellJ E B)^2 := by
  constructor
  · apply energy_density_clock_rate_value ε ω hε hω
    exact hcarrier.trans henergy
  · exact maxwell_clock_fourth_power E B ω hcarrier

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


/-- Stronger chronometric norm theorem: `K=ω⁴` is derived from the carrier identities
rather than supplied independently. -/
theorem optical_covector_norm_from_carrier
    (norm_u K χ ω : ℝ)
    (hu : norm_u = -1)
    (hχ : 0 ≤ χ)
    (hKχ : K = χ^2)
    (hω : ω = Real.sqrt χ) :
    ω^2 * norm_u = - Real.sqrt K := by
  have hrate := clock_rate_square K χ ω hχ hKχ hω
  have hωnonneg : 0 ≤ ω := by
    rw [hω]
    exact Real.sqrt_nonneg χ
  exact optical_covector_norm_scalar norm_u ω K hu hrate.2 hωnonneg

/-! ## 13. Transport/integrability algebra -/

/-- Scalar coefficient identity behind `D_b ω = (ω/4) D_b log K` when `K=ω⁴`. -/
/-- The logarithmic differential of `K=ω⁴` is forced algebraically. -/
theorem quartic_logarithmic_derivative
    (ω dω : ℝ) (hω : ω ≠ 0) :
    (4 * ω^3 * dω) / ω^4 = 4 * dω / ω := by
  field_simp [hω]
  ring

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


/-- Scalar carrier of the Frobenius obstruction `T_O ∧ dT_O`: on the positive-rate
sector its vanishing is exactly vorticity-freeness. -/
def frobeniusObstruction (ω varpi : ℝ) : ℝ := ω^2 * varpi

theorem frobeniusObstruction_zero_iff
    (ω varpi : ℝ) (hω : ω ≠ 0) :
    frobeniusObstruction ω varpi = 0 ↔ varpi = 0 := by
  unfold frobeniusObstruction
  have hw2 : ω^2 ≠ 0 := pow_ne_zero 2 hω
  exact mul_eq_zero_iff_left hw2

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


/-- The exchange-even midpoint and exchange-odd defect are the unique pair reconstructing
the two endpoint values. -/
theorem radar_decomposition_unique
    (θplus θminus T R : ℝ)
    (hplus : T + R = θplus)
    (hminus : T - R = θminus) :
    T = radarTime θplus θminus ∧
    R = radarRadius θplus θminus := by
  constructor <;> unfold radarTime radarRadius <;> linarith

/-- A common shift changes only the clock origin and leaves the radial defect invariant. -/
theorem radar_common_shift (θplus θminus C : ℝ) :
    radarTime (θplus + C) (θminus + C) = radarTime θplus θminus + C ∧
    radarRadius (θplus + C) (θminus + C) = radarRadius θplus θminus := by
  constructor <;> unfold radarTime radarRadius <;> ring


/-- If null synchronization changes both endpoint readings by the same integration constant,
the radial observable is fixed and only the clock origin moves. -/
theorem common_shift_is_only_endpoint_freedom
    (θp θm θp' θm' C : ℝ)
    (hp : θp' = θp + C) (hm : θm' = θm + C) :
    radarTime θp' θm' = radarTime θp θm + C ∧
    radarRadius θp' θm' = radarRadius θp θm := by
  rw [hp, hm]
  exact radar_common_shift θp θm C

/-- Coincident endpoints force vanishing relative radius. -/
@[simp] theorem radarRadius_self (θ : ℝ) : radarRadius θ θ = 0 := by
  unfold radarRadius
  ring


/-! ### Causal endpoint value algebra -/

/-- Abstract past endpoint used by the global causal-order construction. -/
def pastEndpoint (S : Set ℝ) : ℝ := sSup S

/-- Abstract future endpoint used by the global causal-order construction. -/
def futureEndpoint (S : Set ℝ) : ℝ := sInf S


/-- Extended-real past endpoint, including the paper's empty-set convention automatically. -/
def pastEndpointE (S : Set ℝ) : EReal :=
  sSup ((fun θ : ℝ => (θ : EReal)) '' S)

/-- Extended-real future endpoint, including the paper's empty-set convention automatically. -/
def futureEndpointE (S : Set ℝ) : EReal :=
  sInf ((fun θ : ℝ => (θ : EReal)) '' S)

@[simp] theorem pastEndpointE_empty :
    pastEndpointE (∅ : Set ℝ) = (⊥ : EReal) := by
  simp [pastEndpointE]

@[simp] theorem futureEndpointE_empty :
    futureEndpointE (∅ : Set ℝ) = (⊤ : EReal) := by
  simp [futureEndpointE]

/-- Causal past enlargement is monotone even when an endpoint is infinite. -/
theorem pastEndpointE_mono
    {S T : Set ℝ} (h : S ⊆ T) :
    pastEndpointE S ≤ pastEndpointE T := by
  unfold pastEndpointE
  exact sSup_le_sSup (Set.image_mono h)

/-- Future-set shrinkage is monotone even through horizon/endpoint loss. -/
theorem futureEndpointE_mono_of_reverse_inclusion
    {S T : Set ℝ} (h : T ⊆ S) :
    futureEndpointE S ≤ futureEndpointE T := by
  unfold futureEndpointE
  exact sInf_le_sInf (Set.image_mono h)

/-- Thus causal push-up orders both extended endpoints without any finiteness hypothesis. -/
theorem causal_extended_endpoints_mono
    {P₁ P₂ F₁ F₂ : Set ℝ}
    (hP : P₁ ⊆ P₂) (hF : F₂ ⊆ F₁) :
    pastEndpointE P₁ ≤ pastEndpointE P₂ ∧
    futureEndpointE F₁ ≤ futureEndpointE F₂ :=
  ⟨pastEndpointE_mono hP, futureEndpointE_mono_of_reverse_inclusion hF⟩

/-- Enlargement of a nonempty bounded-above chronological past can only increase its endpoint. -/
theorem pastEndpoint_mono
    {S T : Set ℝ}
    (hT : BddAbove T) (hS : S.Nonempty) (hST : S ⊆ T) :
    pastEndpoint S ≤ pastEndpoint T := by
  exact csSup_le_csSup hT hS hST

/-- Shrinking a nonempty future set can only increase its infimum endpoint.
This is the order-theoretic half of causal push-up for the future endpoint. -/
theorem futureEndpoint_mono_of_reverse_inclusion
    {S T : Set ℝ}
    (hS : BddBelow S) (hT : T.Nonempty) (hTS : T ⊆ S) :
    futureEndpoint S ≤ futureEndpoint T := by
  exact csInf_le_csInf hS hT hTS

/-- If causal push-up enlarges the past set and shrinks the future set, both null endpoints
are monotone and therefore so is their exchange-even radar midpoint. -/
theorem causal_radar_clock_mono
    {P₁ P₂ F₁ F₂ : Set ℝ}
    (hP₂bdd : BddAbove P₂) (hP₁ne : P₁.Nonempty)
    (hP : P₁ ⊆ P₂)
    (hF₁bdd : BddBelow F₁) (hF₂ne : F₂.Nonempty)
    (hF : F₂ ⊆ F₁) :
    radarTime (futureEndpoint F₁) (pastEndpoint P₁) ≤
      radarTime (futureEndpoint F₂) (pastEndpoint P₂) := by
  have hp : pastEndpoint P₁ ≤ pastEndpoint P₂ :=
    pastEndpoint_mono hP₂bdd hP₁ne hP
  have hf : futureEndpoint F₁ ≤ futureEndpoint F₂ :=
    futureEndpoint_mono_of_reverse_inclusion hF₁bdd hF₂ne hF
  unfold radarTime
  linarith


/-- Endpoint values depend only on the causal-order sets, not on any choice of connecting
null-geodesic branch used to describe their boundaries. -/
theorem causal_endpoints_branch_independent
    {P₁ P₂ F₁ F₂ : Set ℝ}
    (hP : P₁ = P₂) (hF : F₁ = F₂) :
    pastEndpoint P₁ = pastEndpoint P₂ ∧
    futureEndpoint F₁ = futureEndpoint F₂ := by
  subst P₂
  subst F₂
  exact ⟨rfl, rfl⟩

/-- On the finite endpoint domain, endpoint ordering forces a nonnegative radar radius and
places the midpoint between the two endpoints. -/
theorem radar_order_geometry
    (θminus θplus : ℝ) (h : θminus ≤ θplus) :
    0 ≤ radarRadius θplus θminus ∧
    θminus ≤ radarTime θplus θminus ∧
    radarTime θplus θminus ≤ θplus := by
  unfold radarRadius radarTime
  constructor
  · linarith
  · constructor <;> linarith

/-- Algebraic certificate of the paper's radial-jet statement: coincident endpoint
values have zero odd radar defect, while their principal half-difference is the
nonzero radial covector `R_O`. -/
theorem radialjet_certificate (θ : ℝ) :
    radarRadius θ θ = 0 ∧
    (1 / 2 : ℝ) • (principalThetaPlus - principalThetaMinus) = RO ∧
    RO ≠ 0 := by
  refine ⟨radarRadius_self θ, (principal_endpoint_split).2, RO_ne_zero⟩


/-! ### Implicit null-endpoint differentiation algebra -/

section EndpointDifferentiation

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Linearized endpoint condition
`d_x σ + σ_θ dΘ = 0` forces the endpoint covector uniquely whenever `σ_θ ≠ 0`. -/
theorem implicit_endpoint_covector
    (sigmaX dTheta : W) (sigmaTheta : ℝ)
    (hden : sigmaTheta ≠ 0)
    (hlin : sigmaX + sigmaTheta • dTheta = 0) :
    dTheta = (-sigmaTheta⁻¹) • sigmaX := by
  have hsd : sigmaTheta • dTheta = -sigmaX :=
    eq_neg_of_add_eq_zero_right hlin
  calc
    dTheta = (sigmaTheta⁻¹ * sigmaTheta) • dTheta := by
      rw [inv_mul_cancel₀ hden, one_smul]
    _ = sigmaTheta⁻¹ • (sigmaTheta • dTheta) := by
      rw [smul_smul]
    _ = sigmaTheta⁻¹ • (-sigmaX) := by rw [hsd]
    _ = (-sigmaTheta⁻¹) • sigmaX := by
      simp

end EndpointDifferentiation

/- Abstract symmetric bilinear form, enough to prove the null sum/difference closure. -/
section OpticalClosure

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

variable (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)

/-- Symmetric bilinear evaluation abbreviation. -/
def bil (x y : W) : ℝ := B x y


/-- Scalar rescaling preserves nullness of a covector. -/
theorem bil_smul_self
    (c : ℝ) (x : W) :
    bil B (c • x) (c • x) = c^2 * bil B x x := by
  simp [bil, pow_two]
  ring

/-- Therefore the implicit endpoint covector is null whenever the world-function
covector entering the endpoint equation is null. -/
theorem implicit_endpoint_covector_null
    (sigmaX dTheta : W) (sigmaTheta : ℝ)
    (hden : sigmaTheta ≠ 0)
    (hlin : sigmaX + sigmaTheta • dTheta = 0)
    (hnull : bil B sigmaX sigmaX = 0) :
    bil B dTheta dTheta = 0 := by
  have hsolve :=
    implicit_endpoint_covector sigmaX dTheta sigmaTheta hden hlin
  rw [hsolve, bil_smul_self]
  rw [hnull]
  ring

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

/-- Conversely, orthogonality and equal-opposite norms force both exchanged combinations null. -/
theorem orthogonal_equal_opposite_implies_null_pair
    (hsym : ∀ x y, bil B x y = bil B y x)
    (T R : W)
    (horth : bil B T R = 0)
    (hnorm : -(bil B T T) = bil B R R) :
    bil B (T + R) (T + R) = 0 ∧
    bil B (T - R) (T - R) = 0 := by
  have hsym' : ∀ x y, B x y = B y x := by
    intro x y
    exact hsym x y
  constructor
  · simp only [bil, map_add, LinearMap.add_apply]
    rw [hsym' R T]
    change (B T) T + (B T) R + ((B T) R + (B R) R) = 0
    change (B T) R = 0 at horth
    change -((B T) T) = (B R) R at hnorm
    linarith
  · simp only [bil, map_sub, LinearMap.sub_apply]
    rw [hsym' R T]
    change (B T) T - (B T) R - ((B T) R - (B R) R) = 0
    change (B T) R = 0 at horth
    change -((B T) T) = (B R) R at hnorm
    linarith

/-- The two-null-eikonal formulation is therefore exactly equivalent to the orthogonal
equal-and-opposite-norm optical closure. -/
theorem null_pair_closure_iff
    (hsym : ∀ x y, bil B x y = bil B y x)
    (T R : W) :
    (bil B (T + R) (T + R) = 0 ∧
     bil B (T - R) (T - R) = 0) ↔
    (bil B T R = 0 ∧ -(bil B T T) = bil B R R) := by
  constructor
  · rintro ⟨hp, hm⟩
    exact ⟨null_pair_orthogonal B hsym T R hp hm,
      null_pair_equal_opposite_norm B hsym T R hp hm⟩
  · rintro ⟨ho, hn⟩
    exact orthogonal_equal_opposite_implies_null_pair B hsym T R ho hn

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


/-- Coordinate one-form `dΘ` on the finite-dimensional clock cover. -/
def clockDTheta : R2 →ₗ[ℝ] ℝ where
  toFun v := v.1
  map_add' x y := by simp
  map_smul' c x := by simp

/-- Coordinate one-form `dκ` on the finite-dimensional clock cover. -/
def clockDKappa : R2 →ₗ[ℝ] ℝ where
  toFun v := v.2
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The symplectic form is literally `dκ ∧ dΘ`. -/
theorem clockOmega_eq_dKappa_wedge_dTheta (v w : R2) :
    clockOmega v w =
      clockDKappa v * clockDTheta w - clockDKappa w * clockDTheta v := by
  rcases v with ⟨vΘ, vκ⟩
  rcases w with ⟨wΘ, wκ⟩
  simp [clockOmega, clockDTheta, clockDKappa]
  ring


/-- Canonical Poisson pairing on clock-cover coordinate differentials. -/
def clockPoisson (df dg : R2) : ℝ :=
  df.1 * dg.2 - df.2 * dg.1

/-- Coordinate tangent vectors. -/
def dThetaVec : R2 := (1,0)
def dKappaVec : R2 := (0,1)

@[simp] theorem clockOmega_coordinates :
    clockOmega dKappaVec dThetaVec = 1 ∧
    clockOmega dThetaVec dKappaVec = -1 := by
  norm_num [clockOmega, dThetaVec, dKappaVec]


/-- The homogeneous clock variables are a canonical conjugate pair. -/
@[simp] theorem clockPoisson_coordinates :
    clockPoisson dThetaVec dKappaVec = 1 ∧
    clockPoisson dKappaVec dThetaVec = -1 := by
  norm_num [clockPoisson, dThetaVec, dKappaVec]


/-- Euler/common-scale vector on the positive clock cover. -/
def clockEuler (κ : ℝ) : R2 := (0, κ)

/-- Homogeneous Liouville one-form `κ dΘ` evaluated on a tangent vector. -/
def clockLiouville (κ : ℝ) (v : R2) : ℝ := κ * v.1

/-- The Liouville one-form is exactly contraction of the clock symplectic form with
the common-scale Euler direction. -/
theorem clockLiouville_eq_contraction (κ : ℝ) (v : R2) :
    clockOmega (clockEuler κ) v = clockLiouville κ v := by
  rcases v with ⟨vΘ, vκ⟩
  simp [clockOmega, clockEuler, clockLiouville]

/-- Common-scale dilation acts with weight one on the Liouville primitive. -/
theorem clockLiouville_homogeneous (c κ : ℝ) (v : R2) :
    clockLiouville (c * κ) v = c * clockLiouville κ v := by
  simp [clockLiouville]
  ring


/-- On the unit common-scale section `κ=1`, the homogeneous Liouville primitive is
literally the descended clock one-form `dΘ`. -/
theorem clockLiouville_unit_section (v : R2) :
    clockLiouville 1 v = clockDTheta v := by
  rcases v with ⟨vΘ, vκ⟩
  simp [clockLiouville, clockDTheta]

/-- Tangency to the unit-scale section means no `κ` component. -/
def tangentToClockSection (v : R2) : Prop :=
  v.2 = 0

@[simp] theorem dThetaVec_tangentToClockSection :
    tangentToClockSection dThetaVec := by
  simp [tangentToClockSection, dThetaVec]

@[simp] theorem clockLiouville_unit_dThetaVec :
    clockLiouville 1 dThetaVec = 1 := by
  norm_num [clockLiouville, dThetaVec]

/-- The unit-scale section has a unique tangent direction normalized by the clock one-form:
this is the finite-dimensional Reeb/clock vector. -/
theorem clock_section_reeb_unique
    (v : R2)
    (htan : tangentToClockSection v)
    (hnorm : clockLiouville 1 v = 1) :
    v = dThetaVec := by
  rcases v with ⟨vΘ, vκ⟩
  simp [tangentToClockSection] at htan
  simp [clockLiouville] at hnorm
  subst vκ
  ext <;> simp [dThetaVec, hnorm]

/-- Thus the clock-cover Reeb vector is forced to be `∂Θ` on `κ=1`. -/
theorem clock_section_reeb_existsUnique :
    ∃! v : R2,
      tangentToClockSection v ∧ clockLiouville 1 v = 1 := by
  refine ⟨dThetaVec,
    ⟨dThetaVec_tangentToClockSection, clockLiouville_unit_dThetaVec⟩, ?_⟩
  intro v hv
  exact clock_section_reeb_unique v hv.1 hv.2


/-- Tangent action of positive common-scale dilation on the clock cover. -/
def clockDilationTangent (c : ℝ) (v : R2) : R2 :=
  (v.1, c * v.2)

/-- The exact clock-cover symplectic form is homogeneous of degree one under common scale. -/
theorem clockOmega_dilation_homogeneous
    (c : ℝ) (v w : R2) :
    clockOmega (clockDilationTangent c v) (clockDilationTangent c w) =
      c * clockOmega v w := by
  rcases v with ⟨vΘ, vκ⟩
  rcases w with ⟨wΘ, wκ⟩
  simp [clockOmega, clockDilationTangent]
  ring

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

/-! ## 16. Relational evolution: characteristic-flow form -/

section RelationalFlow

variable {X : Type*}

/-- Reduced relational observable obtained by translating the characteristic-flow
parameter by the intrinsic clock reading. -/
def relationalObservable
    (flow : ℝ → X → X) (F : X → ℝ) (T : X → ℝ)
    (θ : ℝ) (x : X) : ℝ :=
  F (flow (θ - T x) x)

/-- Generator transported along the same characteristic flow. -/
def relationalGeneratorObservable
    (flow : ℝ → X → X) (XF : X → ℝ) (T : X → ℝ)
    (θ : ℝ) (x : X) : ℝ :=
  XF (flow (θ - T x) x)

/-- If `XF` is the derivative of `F` along the characteristic flow, the relational
observable evolves with precisely that generator and no extra clock term. -/
theorem relationalObservable_hasDerivAt
    (flow : ℝ → X → X) (F XF : X → ℝ) (T : X → ℝ)
    (θ : ℝ) (x : X)
    (hgen :
      ∀ t : ℝ, ∀ y : X,
        HasDerivAt (fun s : ℝ => F (flow s y))
          (XF (flow t y)) t) :
    HasDerivAt
      (fun ϑ : ℝ => relationalObservable flow F T ϑ x)
      (relationalGeneratorObservable flow XF T θ x) θ := by
  unfold relationalObservable relationalGeneratorObservable
  exact HasDerivAt.comp_sub_const θ (T x) (hgen (θ - T x) x)

/-- Derivative form of the paper's relational-evolution equation. -/
theorem relationalObservable_deriv
    (flow : ℝ → X → X) (F XF : X → ℝ) (T : X → ℝ)
    (θ : ℝ) (x : X)
    (hgen :
      ∀ t : ℝ, ∀ y : X,
        HasDerivAt (fun s : ℝ => F (flow s y))
          (XF (flow t y)) t) :
    deriv (fun ϑ : ℝ => relationalObservable flow F T ϑ x) θ =
      relationalGeneratorObservable flow XF T θ x :=
  (relationalObservable_hasDerivAt flow F XF T θ x hgen).deriv

/-- If the clock advances by the flow parameter and the characteristic flow composes
additively, the complete relational observable is constant along gauge orbits. -/
theorem relationalObservable_gauge_invariant
    (flow : ℝ → X → X) (F : X → ℝ) (T : X → ℝ)
    (θ t : ℝ) (x : X)
    (hflow : ∀ a b : ℝ, ∀ y : X,
      flow a (flow b y) = flow (a + b) y)
    (hclock : ∀ b : ℝ, ∀ y : X,
      T (flow b y) = T y + b) :
    relationalObservable flow F T θ (flow t x) =
      relationalObservable flow F T θ x := by
  unfold relationalObservable
  rw [hclock t x, hflow]
  congr 2
  ring

/-- At the intrinsic clock reading, the relational observable reduces to the original
observable whenever zero flow is the identity. -/
theorem relationalObservable_at_clock
    (flow : ℝ → X → X) (F : X → ℝ) (T : X → ℝ)
    (x : X)
    (hzero : ∀ y : X, flow 0 y = y) :
    relationalObservable flow F T (T x) x = F x := by
  unfold relationalObservable
  rw [sub_self, hzero]

/-- The transported generator observable is gauge invariant under the same hypotheses. -/
theorem relationalGeneratorObservable_gauge_invariant
    (flow : ℝ → X → X) (XF : X → ℝ) (T : X → ℝ)
    (θ t : ℝ) (x : X)
    (hflow : ∀ a b : ℝ, ∀ y : X,
      flow a (flow b y) = flow (a + b) y)
    (hclock : ∀ b : ℝ, ∀ y : X,
      T (flow b y) = T y + b) :
    relationalGeneratorObservable flow XF T θ (flow t x) =
      relationalGeneratorObservable flow XF T θ x := by
  unfold relationalGeneratorObservable
  rw [hclock t x, hflow]
  congr 2
  ring

end RelationalFlow

/-! ### Scalar translation specialization -/

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


/-- Kerr-Newman `Σ` is nonnegative everywhere in this scalar model. -/
theorem Sigma_nonneg (r a θ : ℝ) :
    0 ≤ Sigma r a θ := by
  unfold Sigma
  nlinarith [sq_nonneg r, sq_nonneg (a * Real.cos θ)]

/-- Its zero stratum is exactly where both squared contributions vanish. -/
theorem Sigma_eq_zero_iff (r a θ : ℝ) :
    Sigma r a θ = 0 ↔ r = 0 ∧ a * Real.cos θ = 0 := by
  constructor
  · intro h
    have hr2 : r^2 = 0 := by
      unfold Sigma at h
      nlinarith [sq_nonneg (a * Real.cos θ)]
    have ha2 : (a * Real.cos θ)^2 = 0 := by
      unfold Sigma at h
      nlinarith [sq_nonneg r]
    exact ⟨sq_eq_zero_iff.mp hr2, sq_eq_zero_iff.mp ha2⟩
  · rintro ⟨rfl, ha⟩
    unfold Sigma
    have ha2 : (a * Real.cos θ)^2 = 0 := by
      rw [ha]
      norm_num
    nlinarith



/-- Radial derivative of the Kerr-Newman separability scalar. -/
theorem Sigma_hasDerivAt_r (r a θ : ℝ) :
    HasDerivAt (fun x : ℝ => Sigma x a θ) (2 * r) r := by
  unfold Sigma
  convert ((hasDerivAt_id r).pow 2).add_const (a^2 * (Real.cos θ)^2) using 1 <;> ring

/-- Principal-frame electric component of the Kerr-Newman Maxwell field. -/
def kerrPrincipalE (Q r a θ : ℝ) : ℝ :=
  Q * (r^2 - a^2 * (Real.cos θ)^2) / (Sigma r a θ)^2

/-- Principal-frame magnetic component of the Kerr-Newman Maxwell field. -/
def kerrPrincipalB (Q r a θ : ℝ) : ℝ :=
  2 * Q * a * r * Real.cos θ / (Sigma r a θ)^2

/-- The Kerr-Newman principal electromagnetic magnitude collapses exactly to `Q²/Σ²`.
This is the algebraic identity behind the curvature carrier and requires no curvature tensor
calculation once the principal Maxwell components are known. -/
theorem kerrPrincipal_field_magnitude
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    (kerrPrincipalE Q r a θ)^2 + (kerrPrincipalB Q r a θ)^2 =
      Q^2 / (Sigma r a θ)^2 := by
  unfold kerrPrincipalE kerrPrincipalB
  field_simp [hsig]
  unfold Sigma
  ring

/-- Hence the general principal Maxwell carrier `2(E²+B²)` becomes the manuscript's
Kerr-Newman carrier `2Q²/Σ²`. -/
theorem kerrPrincipalChi_formula
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    principalChi (kerrPrincipalE Q r a θ) (kerrPrincipalB Q r a θ) =
      2 * Q^2 / (Sigma r a θ)^2 := by
  unfold principalChi
  rw [kerrPrincipal_field_magnitude Q r a θ hsig]

/-- Scalar Kerr-Newman carrier magnitude before introducing the full tensor geometry. -/
def kerrChiScalar (Q r a θ : ℝ) : ℝ :=
  2 * Q^2 / (Sigma r a θ)^2

/-- The named Kerr carrier is not an independent definition: it is exactly the invariant
principal Maxwell magnitude of the explicit field components. -/
theorem kerrChiScalar_eq_principalChi
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    kerrChiScalar Q r a θ =
      principalChi (kerrPrincipalE Q r a θ) (kerrPrincipalB Q r a θ) := by
  rw [kerrPrincipalChi_formula Q r a θ hsig]
  rfl


/-- Ricci norm reconstructed directly from the principal Einstein-Maxwell carrier. -/
def kerrRicciNormScalar (Q r a θ : ℝ) : ℝ :=
  principalRicciNormFromCarrier
    (principalChi
      (kerrPrincipalE Q r a θ)
      (kerrPrincipalB Q r a θ))

/-- The advertised Kerr-Newman Ricci norm is now a theorem of the principal Maxwell field,
not an imported curvature formula. -/
theorem kerrRicciNormScalar_formula
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    kerrRicciNormScalar Q r a θ =
      4 * Q^4 / (Sigma r a θ)^4 := by
  rw [kerrRicciNormScalar, principalRicciNormFromCarrier_eq,
    kerrPrincipalChi_formula Q r a θ hsig]
  field_simp [hsig]
  ring

/-- By construction the Kerr Ricci norm is identically the square of the principal carrier. -/
theorem kerrRicciNormScalar_eq_carrier_sq
    (Q r a θ : ℝ) :
    kerrRicciNormScalar Q r a θ =
      (principalChi
        (kerrPrincipalE Q r a θ)
        (kerrPrincipalB Q r a θ))^2 := by
  simp [kerrRicciNormScalar, principalRicciNormFromCarrier_eq]

/-- The squared Maxwell invariants of Kerr-Newman therefore give `4Q⁴/Σ⁴` directly. -/
theorem kerrMaxwellInvariantMagnitude
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    (maxwellI (kerrPrincipalE Q r a θ) (kerrPrincipalB Q r a θ))^2 +
      (maxwellJ (kerrPrincipalE Q r a θ) (kerrPrincipalB Q r a θ))^2 =
      4 * Q^4 / (Sigma r a θ)^4 := by
  rw [maxwell_invariants_eq_principalChi_sq]
  rw [kerrPrincipalChi_formula Q r a θ hsig]
  field_simp [hsig]
  ring

/-- Therefore the Kerr-Newman Ricci-norm formula follows from the universal
Einstein-Maxwell carrier identity `K=χ²` plus the explicit principal Maxwell field,
without a separate Kerr curvature computation. -/
theorem kerrRicciNorm_from_principal_EM
    (Q r a θ K : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hKcarrier :
      K =
        (principalChi
          (kerrPrincipalE Q r a θ)
          (kerrPrincipalB Q r a θ))^2) :
    K = 4 * Q^4 / (Sigma r a θ)^4 := by
  rw [hKcarrier, kerrPrincipalChi_formula Q r a θ hsig]
  field_simp [hsig]
  ring


/-- The Kerr-Newman electromagnetic carrier is strictly positive on the regular charged sector. -/
theorem kerrChiScalar_pos
    (Q r a θ : ℝ)
    (hQ : Q ≠ 0) (hsig : Sigma r a θ ≠ 0) :
    0 < kerrChiScalar Q r a θ := by
  unfold kerrChiScalar
  have hq2 : 0 < Q^2 := sq_pos_of_ne_zero hQ
  have hs2 : 0 < (Sigma r a θ)^2 := sq_pos_of_ne_zero hsig
  positivity

/-- Squaring the carrier gives exactly the Kerr-Newman invariant magnitude appearing in the paper. -/
theorem kerrChiScalar_sq
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    (kerrChiScalar Q r a θ)^2 =
      4 * Q^4 / (Sigma r a θ)^4 := by
  unfold kerrChiScalar
  field_simp [hsig]
  ring

/-- Hence if the Ricci norm is identified with `χ²`, its advertised Kerr-Newman form follows. -/
theorem kerrRicciNorm_from_carrier
    (Q r a θ K : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hK : K = (kerrChiScalar Q r a θ)^2) :
    K = 4 * Q^4 / (Sigma r a θ)^4 := by
  rw [hK, kerrChiScalar_sq Q r a θ hsig]

/-- Its radial derivative is forced by `Σ`. -/
theorem kerrChiScalar_hasDerivAt_r
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt (fun x : ℝ => kerrChiScalar Q x a θ)
      (-8 * Q^2 * r / (Sigma r a θ)^3) r := by
  have hs := Sigma_hasDerivAt_r r a θ
  have hd := hs.pow 2
  have hn : HasDerivAt (fun _ : ℝ => 2 * Q^2) 0 r :=
    hasDerivAt_const r (2 * Q^2)
  have hraw := hn.fun_div hd (pow_ne_zero 2 hsig)
  change HasDerivAt
    (fun x : ℝ => 2 * Q^2 / (Sigma x a θ)^2)
    (-8 * Q^2 * r / (Sigma r a θ)^3) r
  convert hraw using 1
  field_simp [hsig]
  ring

/-- The radial logarithmic derivative is exactly the formula used by the manuscript:
`∂ᵣ log χ = -4r/Σ`. -/
theorem kerrLogChi_hasDerivAt_r
    (Q r a θ : ℝ)
    (hQ : Q ≠ 0) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log (kerrChiScalar Q x a θ))
      (-4 * r / Sigma r a θ) r := by
  have hchi := kerrChiScalar_hasDerivAt_r Q r a θ hsig
  have hchi0 : kerrChiScalar Q r a θ ≠ 0 := by
    unfold kerrChiScalar
    exact div_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hQ))
      (pow_ne_zero 2 hsig)
  have hlog := hchi.log hchi0
  convert hlog using 1
  unfold kerrChiScalar
  field_simp [hQ, hsig]
  ring


/-- On a regular Kerr-Newman point the first radial carrier gradient resolves the boost
exactly away from the `r=0` degeneracy stratum. -/
theorem kerrRadialLogGradient_ne_zero_iff
    (r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    (-4 * r / Sigma r a θ ≠ 0) ↔ r ≠ 0 := by
  constructor
  · intro h hr
    apply h
    simp [hr]
  · intro hr
    exact div_ne_zero (mul_ne_zero (by norm_num) hr) hsig


/-- Radial carrier-gradient coefficient selecting the residual Kerr-Newman boost. -/
def kerrRadialGradient (r a θ : ℝ) : ℝ :=
  -4 * r / Sigma r a θ

/-- A purely radial principal covector has equal-and-opposite null components; the common
normalization is irrelevant to the balance. -/
def kerrGradientQMinus (r a θ : ℝ) : ℝ :=
  kerrRadialGradient r a θ

def kerrGradientQPlus (r a θ : ℝ) : ℝ :=
  - kerrRadialGradient r a θ

/-- On the regular `r ≠ 0` stratum the Kerr carrier gradient genuinely resolves the boost. -/
theorem kerrGradientQMinus_ne_zero
    (r a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hr : r ≠ 0) :
    kerrGradientQMinus r a θ ≠ 0 := by
  unfold kerrGradientQMinus kerrRadialGradient
  exact (kerrRadialLogGradient_ne_zero_iff r a θ hsig).2 hr

/-- Therefore the unique carrier-selected residual rapidity in the canonical principal
Kerr-Newman frame is exactly zero. -/
theorem kerrCarrier_balance_rapidity_zero
    (r a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hr : r ≠ 0) :
    sigmaStar
      (kerrGradientQMinus r a θ)
      (kerrGradientQPlus r a θ) = 0 := by
  have hq := kerrGradientQMinus_ne_zero r a θ hsig hr
  unfold kerrGradientQPlus
  exact sigmaStar_opposite_components
    (kerrGradientQMinus r a θ) hq

/-- Equivalently, the carrier-selected observer is the unboosted principal observer. -/
theorem kerrCarrier_balanced_observer_unboosted
    (r a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hr : r ≠ 0) :
    opticalObserver
      (sigmaStar
        (kerrGradientQMinus r a θ)
        (kerrGradientQPlus r a θ)) = TO := by
  rw [kerrCarrier_balance_rapidity_zero r a θ hsig hr]
  ext <;> norm_num [opticalObserver, TO]


/-- Radial derivative of the first carrier-gradient coefficient. -/
theorem kerrRadialGradient_hasDerivAt
    (r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt (fun x : ℝ => kerrRadialGradient x a θ)
      ((-4 * Sigma r a θ + 8 * r^2) / (Sigma r a θ)^2) r := by
  have hn : HasDerivAt (fun x : ℝ => -4 * x) (-4) r :=
    (hasDerivAt_id r).const_mul (-4)
  have hd := Sigma_hasDerivAt_r r a θ
  have hraw := hn.fun_div hd hsig
  unfold kerrRadialGradient
  convert hraw using 1
  field_simp [hsig]
  ring

/-- At the first-gradient degeneracy `r=0`, the second radial jet is `-4/Σ`. -/
theorem kerrRadialGradient_second_at_zero
    (a θ : ℝ) (hsig : Sigma 0 a θ ≠ 0) :
    HasDerivAt (fun x : ℝ => kerrRadialGradient x a θ)
      (-4 / Sigma 0 a θ) 0 := by
  have h := kerrRadialGradient_hasDerivAt 0 a θ hsig
  convert h using 1
  field_simp [hsig]
  ring

/-- That second radial jet is nonzero everywhere on the regular `r=0` stratum. -/
theorem kerrRadialGradient_second_at_zero_ne
    (a θ : ℝ) (hsig : Sigma 0 a θ ≠ 0) :
    -4 / Sigma 0 a θ ≠ 0 := by
  exact div_ne_zero (by norm_num) hsig

/-- Hence every regular Kerr-Newman point is resolved by a finite radial carrier jet:
the first jet when `r ≠ 0`, and the second jet when `r=0`. -/
theorem kerr_regular_first_or_second_radial_jet_resolves
    (r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    kerrRadialGradient r a θ ≠ 0 ∨
      (r = 0 ∧ -4 / Sigma 0 a θ ≠ 0) := by
  by_cases hr : r = 0
  · right
    subst r
    exact ⟨rfl, kerrRadialGradient_second_at_zero_ne a θ hsig⟩
  · left
    unfold kerrRadialGradient
    exact (kerrRadialLogGradient_ne_zero_iff r a θ hsig).2 hr

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


/-- Direct Kerr-Newman clock-rate theorem from the explicit principal Maxwell field and
the universal carrier identity `K=χ²`.  No Kerr-specific curvature formula is supplied. -/
theorem kerrNewman_clock_rate_from_principal_EM
    (Q r a θ K ω : ℝ)
    (hQ : Q ≠ 0)
    (hsigpos : 0 < Sigma r a θ)
    (hKcarrier :
      K =
        (principalChi
          (kerrPrincipalE Q r a θ)
          (kerrPrincipalB Q r a θ))^2)
    (hω : ω = Real.sqrt (Real.sqrt K)) :
    ω = Real.sqrt 2 * |Q| / Sigma r a θ := by
  have hsig : Sigma r a θ ≠ 0 := ne_of_gt hsigpos
  have hchi :
      principalChi
          (kerrPrincipalE Q r a θ)
          (kerrPrincipalB Q r a θ) =
        2 * Q^2 / (Sigma r a θ)^2 :=
    kerrPrincipalChi_formula Q r a θ hsig
  have hchipos :
      0 ≤ principalChi
          (kerrPrincipalE Q r a θ)
          (kerrPrincipalB Q r a θ) :=
    principalChi_nonneg _ _
  have hsqrtK :
      Real.sqrt K =
        principalChi
          (kerrPrincipalE Q r a θ)
          (kerrPrincipalB Q r a θ) := by
    rw [hKcarrier, Real.sqrt_sq_eq_abs, abs_of_nonneg hchipos]
  have hω' :
      ω =
        Real.sqrt
          (principalChi
            (kerrPrincipalE Q r a θ)
            (kerrPrincipalB Q r a θ)) := by
    rw [hω, hsqrtK]
  exact kerrNewman_clock_rate
    Q (Sigma r a θ)
    (principalChi
      (kerrPrincipalE Q r a θ)
      (kerrPrincipalB Q r a θ))
    ω hsigpos hchi hω'


/-- Intrinsic Kerr-Newman clock rate constructed only from the principal Maxwell field. -/
def kerrClockRateFromPrincipalEM (Q r a θ : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (kerrRicciNormScalar Q r a θ))

/-- The explicit principal Maxwell field forces the intrinsic clock rate
`sqrt(2)|Q|/Σ` with no curvature input. -/
theorem kerrClockRateFromPrincipalEM_formula
    (Q r a θ : ℝ)
    (hQ : Q ≠ 0)
    (hsigpos : 0 < Sigma r a θ) :
    kerrClockRateFromPrincipalEM Q r a θ =
      Real.sqrt 2 * |Q| / Sigma r a θ := by
  exact kerrNewman_clock_rate_from_principal_EM
    Q r a θ
    (kerrRicciNormScalar Q r a θ)
    (kerrClockRateFromPrincipalEM Q r a θ)
    hQ hsigpos
    (kerrRicciNormScalar_eq_carrier_sq Q r a θ)
    rfl

/-- Curvature-derived Kerr-Newman separability multiplier. -/
def kerrMultiplier (Q sig : ℝ) : ℝ :=
  sig / (Real.sqrt 2 * |Q|)

/-- Corresponding intrinsic clock rate. -/
def kerrClockRate (Q sig : ℝ) : ℝ :=
  Real.sqrt 2 * |Q| / sig

/-- Away from the vacuum and ring singular strata, the clock rate and multiplier are exact reciprocals. -/
theorem kerrClockRate_mul_multiplier
    (Q sig : ℝ) (hQ : Q ≠ 0) (hsig : sig ≠ 0) :
    kerrClockRate Q sig * kerrMultiplier Q sig = 1 := by
  unfold kerrClockRate kerrMultiplier
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have habs : |Q| ≠ 0 := abs_ne_zero.mpr hQ
  field_simp [hsqrt, habs, hsig]

/-- Equivalently the field-derived clock rate is the inverse separability multiplier. -/
theorem kerrClockRate_eq_inv_multiplier
    (Q sig : ℝ) (_hQ : Q ≠ 0) (_hsig : sig ≠ 0) :
    kerrClockRate Q sig = (kerrMultiplier Q sig)⁻¹ := by
  unfold kerrClockRate kerrMultiplier
  rw [inv_div]

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

/-- Combining the curvature invariant, positive carrier root, and Mino definition
removes the clock-rate formula as an independent premise. -/
theorem kerrNewman_mino_clock_forced
    (Q sig K χ ω dt dlam : ℝ)
    (hsig : 0 < sig) (hQ : Q ≠ 0)
    (hK : K = 4 * Q^4 / sig^4)
    (hχ : χ = Real.sqrt K)
    (hω : ω = Real.sqrt χ)
    (hmino : dlam = dt / sig) :
    ω * dt = Real.sqrt 2 * |Q| * dlam := by
  have hχform := kerrNewman_chi_from_K Q sig K χ hsig hQ hK hχ
  have hw := kerrNewman_clock_rate Q sig χ ω hsig hχform hω
  rw [hw, hmino]
  field_simp [ne_of_gt hsig]
  ring


/-- Mino-clock identity derived directly from the Kerr-Newman principal Maxwell field
and the universal Einstein-Maxwell carrier identity, with no imported `K=4Q⁴/Σ⁴` premise. -/
theorem kerrNewman_mino_clock_from_principal_EM
    (Q r a θ K ω dt dlam : ℝ)
    (hQ : Q ≠ 0)
    (hsigpos : 0 < Sigma r a θ)
    (hKcarrier :
      K =
        (principalChi
          (kerrPrincipalE Q r a θ)
          (kerrPrincipalB Q r a θ))^2)
    (hω : ω = Real.sqrt (Real.sqrt K))
    (hmino : dlam = dt / Sigma r a θ) :
    ω * dt = Real.sqrt 2 * |Q| * dlam := by
  have hw :=
    kerrNewman_clock_rate_from_principal_EM
      Q r a θ K ω hQ hsigpos hKcarrier hω
  rw [hw, hmino]
  field_simp [ne_of_gt hsigpos]
  ring


/-- Fully constructed principal-field version of the Kerr-Newman Mino-clock identity. -/
theorem kerrMinoClockFromPrincipalEM
    (Q r a θ dt dlam : ℝ)
    (hQ : Q ≠ 0)
    (hsigpos : 0 < Sigma r a θ)
    (hmino : dlam = dt / Sigma r a θ) :
    kerrClockRateFromPrincipalEM Q r a θ * dt =
      Real.sqrt 2 * |Q| * dlam := by
  rw [kerrClockRateFromPrincipalEM_formula Q r a θ hQ hsigpos, hmino]
  field_simp [ne_of_gt hsigpos]
  ring

/-- At zero charge the Kerr-Newman Ricci carrier vanishes identically in the scalar specialization. -/
theorem kerrNewman_vacuum_carrier_vanishes
    (sig K χ : ℝ)
    (hK : K = 4 * (0 : ℝ)^4 / sig^4)
    (hχ : χ = Real.sqrt K) :
    χ = 0 := by
  rw [hχ, hK]
  norm_num

/-- Kerr-Newman Carter angular velocity. -/
def carterOmega (r a : ℝ) : ℝ :=
  a / (r^2 + a^2)

/-- Coordinate numerator of the Carter principal observer in the `(∂t,∂φ)` plane. -/
def carterNumerator (r a : ℝ) : R2 :=
  (r^2 + a^2, a)

/-- The Carter numerator is exactly the stationary direction with angular velocity
`Ω_C=a/(r²+a²)`, multiplied by its forced normalization factor. -/
theorem carterNumerator_factorization
    (r a : ℝ) (h : r^2 + a^2 ≠ 0) :
    carterNumerator r a =
      (r^2 + a^2) • ((1 : ℝ), carterOmega r a) := by
  ext
  · simp [carterNumerator]
  · simp [carterNumerator, carterOmega]
    field_simp [h]


/-- The stationary angular velocity of the canonical principal Kerr-Newman direction is
therefore exactly Carter's `Ω_C`. -/
theorem carterNumerator_angular_velocity
    (r a : ℝ) :
    (carterNumerator r a).2 / (carterNumerator r a).1 =
      carterOmega r a := by
  rfl

/-- Combining the carrier-gradient balance with the canonical Kerr-Newman principal
stationary direction gives the algebraic Carter-rest certificate: no residual boost is
applied, and the selected stationary direction has angular velocity `Ω_C`. -/
theorem kerr_relative_rest_carter_certificate
    (r a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hr : r ≠ 0) :
    sigmaStar
      (kerrGradientQMinus r a θ)
      (kerrGradientQPlus r a θ) = 0 ∧
    (carterNumerator r a).2 / (carterNumerator r a).1 =
      carterOmega r a := by
  exact ⟨kerrCarrier_balance_rapidity_zero r a θ hsig hr,
    carterNumerator_angular_velocity r a⟩

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

/-- Minimal remaining algebraic interface to the still-unformalized Iyer-Wald layer.
The response covector is not supplied, its factorization is not supplied, and kernel invisibility
is not supplied.  The only structural premise is the physical statement that the integrated
stress response depends only on the characteristic variation; positivity supplies nonvanishing.
Everything below is derived from those two facts. -/
/-- Even stronger interface: only extensionality of the response with respect to the
characteristic variation and positivity are retained.  Kernel-invisibility and Λ are derived. -/
structure ExtensionalBridgeData where
  beta : P →ₗ[ℝ] KSpace
  ell : P →ₗ[ℝ] ℝ
  response_extensional : ∀ p q : P, beta p = beta q → ell p = ell q
  positiveWitness : P
  response_positive : 0 < ell positiveWitness

theorem ExtensionalBridgeData.kernel_invisible
    (D : ExtensionalBridgeData (P:=P) (KSpace:=KSpace)) :
    LinearMap.ker D.beta ≤ LinearMap.ker D.ell :=
  kernel_invisible_of_response_extensional
    D.beta D.ell D.response_extensional

noncomputable def ExtensionalBridgeData.Lambda
    (D : ExtensionalBridgeData (P:=P) (KSpace:=KSpace)) :
    LinearMap.range D.beta →ₗ[ℝ] ℝ :=
  characteristicCovectorOfKernel D.beta D.ell D.kernel_invisible

theorem extensionalBridge_factorization
    (D : ExtensionalBridgeData (P:=P) (KSpace:=KSpace)) :
    D.Lambda.comp D.beta.rangeRestrict = D.ell :=
  characteristicCovectorOfKernel_factorization
    D.beta D.ell D.kernel_invisible

theorem extensionalBridge_Lambda_nonzero
    (D : ExtensionalBridgeData (P:=P) (KSpace:=KSpace)) :
    D.Lambda ≠ 0 := by
  exact descended_covector_nonzero
    D.beta.rangeRestrict D.Lambda D.ell
    (extensionalBridge_factorization D)
    (covector_nonzero_of_positive D.ell D.positiveWitness D.response_positive)

theorem extensionalBridge_Lambda_unique
    (D : ExtensionalBridgeData (P:=P) (KSpace:=KSpace))
    (Λ' : LinearMap.range D.beta →ₗ[ℝ] ℝ)
    (hΛ' : Λ'.comp D.beta.rangeRestrict = D.ell) :
    Λ' = D.Lambda :=
  characteristicCovectorOfKernel_unique
    D.beta D.ell D.kernel_invisible Λ' hΛ'

theorem extensionalBridge_quotient_finrank_one
    (D : ExtensionalBridgeData (P:=P) (KSpace:=KSpace)) :
    Module.finrank ℝ
      ((LinearMap.range D.beta) ⧸ LinearMap.ker D.Lambda) = 1 :=
  clockQuotient_finrank_one D.Lambda (extensionalBridge_Lambda_nonzero D)

/-- Maxwell-specialized bridge data: positivity is no longer supplied as an abstract witness.
It is forced by the explicit positive Maxwell response on one positive test profile. -/
structure MaxwellBridgeData where
  beta : P →ₗ[ℝ] KSpace
  ell : P →ₗ[ℝ] ℝ
  response_extensional : ∀ p q : P, beta p = beta q → ell p = ell q
  positiveWitness : P
  smear : ℝ
  chi : ℝ
  volume : ℝ
  smear_pos : 0 < smear
  chi_pos : 0 < chi
  volume_pos : 0 < volume
  response_formula :
    ell positiveWitness = maxwellPositiveResponse smear chi volume

theorem MaxwellBridgeData.response_positive
    (D : MaxwellBridgeData (P:=P) (KSpace:=KSpace)) :
    0 < D.ell D.positiveWitness := by
  rw [D.response_formula]
  exact maxwellPositiveResponse_pos
    D.smear D.chi D.volume D.smear_pos D.chi_pos D.volume_pos

theorem MaxwellBridgeData.kernel_invisible
    (D : MaxwellBridgeData (P:=P) (KSpace:=KSpace)) :
    LinearMap.ker D.beta ≤ LinearMap.ker D.ell :=
  kernel_invisible_of_response_extensional
    D.beta D.ell D.response_extensional

/-- The Einstein-Maxwell characteristic clock covector is therefore a construction, not input data. -/
noncomputable def MaxwellBridgeData.Lambda
    (D : MaxwellBridgeData (P:=P) (KSpace:=KSpace)) :
    LinearMap.range D.beta →ₗ[ℝ] ℝ :=
  characteristicCovectorOfKernel D.beta D.ell D.kernel_invisible

theorem maxwellBridge_factorization
    (D : MaxwellBridgeData (P:=P) (KSpace:=KSpace)) :
    D.Lambda.comp D.beta.rangeRestrict = D.ell :=
  characteristicCovectorOfKernel_factorization
    D.beta D.ell D.kernel_invisible

theorem maxwellBridge_Lambda_nonzero
    (D : MaxwellBridgeData (P:=P) (KSpace:=KSpace)) :
    D.Lambda ≠ 0 := by
  exact descended_covector_nonzero
    D.beta.rangeRestrict D.Lambda D.ell
    (maxwellBridge_factorization D)
    (covector_nonzero_of_positive D.ell D.positiveWitness D.response_positive)

theorem maxwellBridge_Lambda_unique
    (D : MaxwellBridgeData (P:=P) (KSpace:=KSpace))
    (Λ' : LinearMap.range D.beta →ₗ[ℝ] ℝ)
    (hΛ' : Λ'.comp D.beta.rangeRestrict = D.ell) :
    Λ' = D.Lambda :=
  characteristicCovectorOfKernel_unique
    D.beta D.ell D.kernel_invisible Λ' hΛ'

theorem maxwellBridge_quotient_finrank_one
    (D : MaxwellBridgeData (P:=P) (KSpace:=KSpace)) :
    Module.finrank ℝ
      ((LinearMap.range D.beta) ⧸ LinearMap.ker D.Lambda) = 1 :=
  clockQuotient_finrank_one D.Lambda (maxwellBridge_Lambda_nonzero D)

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


/-- End-to-end scalar backbone with the Ricci-stress relation itself derived from
the four-dimensional trace-free Einstein-Maxwell equations. -/
theorem scalar_backbone_from_einstein_maxwell
    (D s T Ric metricComp scalarR traceT : ℝ)
    (hrecip : wG D = -(wM D))
    (htracefree : traceT = 0)
    (hEinTrace : einsteinTrace 4 scalarR = 8 * Real.pi * traceT)
    (hEin :
      Ric - (1 / 2 : ℝ) * metricComp * scalarR =
        8 * Real.pi * T) :
    D = 4 ∧
    scalarR = 0 ∧
    (Real.exp (2*s) = 1 ↔ s = 0) ∧
    (-16 * Real.pi * T = -2 * Ric) ∧
    ((Real.exp s - Real.exp (-s)) /
      (Real.exp s + Real.exp (-s)) = Real.tanh s) := by
  have hD : D = 4 := (reciprocal_weights_iff_four D).mp hrecip
  have hR :
      scalarR = 0 :=
    four_dimensional_tracefree_einstein_scalar_zero
      scalarR traceT htracefree hEinTrace
  have hjet :
      -16 * Real.pi * T = -2 * Ric :=
    jet_eq_minus_two_ricci_from_einstein_maxwell
      Ric metricComp scalarR traceT T htracefree hEinTrace hEin
  exact ⟨hD, hR, exp_two_eq_one_iff s, hjet, optical_defect_is_tanh s⟩

/-! ## 20. Audit sentinels -/

#check reciprocal_weights_iff_four
#check mobius_projective_unique
#check solution_preserving_fixed_point
#check defect_hasDerivAt_zero
#check principalStress_sq
#check principalStress_trace_sq
#check principalStress_rainich
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
#check characteristic_range_restriction_surjective
#check descended_covector_unique
#check null_pair_orthogonal
#check mino_clock_identity
#check scalar_backbone
#check opticalBilinear_TO
#check opticalBilinear_RO
#check opticalBilinear_TO_RO
#check principal_endpoint_covectors_null
#check implicit_endpoint_covector
#check bil_smul_self
#check implicit_endpoint_covector_null
#check relationalObservable_hasDerivAt
#check relationalObservable_deriv
#check relationalObservable_gauge_invariant
#check relationalObservable_at_clock
#check relationalGeneratorObservable_gauge_invariant
#check principalJetFromFApply_eq_principalJetApply
#check principalNormalizedJetFromFApply_eq_involution
#check principalFieldDerived_lorentz_basis_eigen_plus
#check principalFieldDerived_transverse_basis_eigen_minus
#check principalMaxwellStarF_skew
#check principalMaxwellStar_sq
#check principalMaxwellFStarF_eq_maxwellJ
#check principalMaxwell_invariants_from_forms
#check principalMaxwell_form_invariant_magnitude
#check principalStressFromF_trace_zero
#check principalStressFromF_trace_sq
#check principalStressFromF_rainich
#check principalJetFromF_eq_neg_principalStress
#check principalJetFromF_sq
#check principalJetFromF_rainich
#check principalMaxwellF_skew
#check principalMaxwellFsq_eq_maxwellI
#check principalStressFromF_eq_principalStress
#check principalFieldEnergyDensity_eq_chi
#check principalStress_time_eigen
#check principalStress_space_eigen
#check principalMaxwell_timelike_eigen_from_chi
#check principalEnergyDensity_pos
#check principalEnergyDensity_recovers_chi
#check principalRicciNormFromCarrier_eq
#check kerrRicciNormScalar
#check kerrRicciNormScalar_formula
#check kerrRicciNormScalar_eq_carrier_sq
#check kerrClockRateFromPrincipalEM
#check kerrClockRateFromPrincipalEM_formula
#check kerrMinoClockFromPrincipalEM
#check Xi_product_eq_kappa_sq
#check character_common_scale_sqrt
#check gravScaleExponent_from_primitive_weights
#check maxwellMetricScaleExponent_from_primitive_weights
#check gravity_relative_weight_from_primitive_counts
#check maxwell_relative_weight_from_primitive_counts
#check primitive_relative_weights_reciprocal_iff_four
#check lambdaUS_div_rhoUS
#check maxwellStressScaleFactor_US
#check rescaled_field_equation_weight
#check rescaled_solution_preserving_iff
#check kerrRadialGradient_hasDerivAt
#check kerrRadialGradient_second_at_zero
#check kerrRadialGradient_second_at_zero_ne
#check kerr_regular_first_or_second_radial_jet_resolves
#check kerrRadialGradient
#check kerrGradientQMinus_ne_zero
#check kerrCarrier_balance_rapidity_zero
#check kerrCarrier_balanced_observer_unboosted
#check carterNumerator_angular_velocity
#check kerr_relative_rest_carter_certificate
#check quotientBilinearForm
#check quotientBilinearForm_mk
#check quotientBilinearForm_unique
#check quotientBilinearForm_skew
#check skew_right_radical_of_left
#check skewQuotientBilinearForm
#check covectorScaleMap
#check covectorScaleMap_bijective
#check normalizedCovectorDualEquiv
#check clockQuotientDualEquiv
#check clockLiouville_unit_section
#check dThetaVec_tangentToClockSection
#check clockLiouville_unit_dThetaVec
#check clock_section_reeb_unique
#check clock_section_reeb_existsUnique
#check conformalUnitFactor_metric_cancel
#check conformal_unit_timelike_normalization
#check conformal_dual_scale
#check conformal_dual_scale_eq_clock_rate
#check principalJet_local_decomposition
#check principalSpatialRemainder_time_zero
#check principalRestrictedResponse_unit
#check principalRestrictedResponse_factor
#check principalLocalClockRatio_forced
#check principalTO_unit
#check relativeConstraintResidual_eq_sinh
#check relativeConstraintResidual_hasDerivAt_zero
#check relativeConstraintResidual_deriv_zero
#check iyerWald_bulk_response_from_relative_scaling
#check characteristic_half_contraction_from_relative_scaling
#check optical_covector_norm_from_carrier
#check kerrPrincipal_field_magnitude
#check kerrPrincipalChi_formula
#check kerrChiScalar_eq_principalChi
#check kerrMaxwellInvariantMagnitude
#check kerrRicciNorm_from_principal_EM
#check kerrNewman_clock_rate_from_principal_EM
#check kerrNewman_mino_clock_from_principal_EM
#check scaledResidual_odd_iteratedDeriv_eq_minus_two_ricci_from_EM
#check scaledResidual_first_jet_eq_minus_two_ricci_from_EM
#check maxwellStressTraceFactor_four
#check maxwellStressTraceFactor_zero_iff_four
#check four_dimensional_tracefree_einstein_scalar_zero
#check einstein_component_to_ricci
#check einstein_maxwell_ricci_forced
#check jet_eq_minus_two_ricci_from_einstein_maxwell
#check scalar_backbone_from_einstein_maxwell
#check principalJetApply_eq_neg_stress
#check principal_plane_decomposition
#check principalLorentzPart_eigen_plus
#check principalTransversePart_eigen_minus
#check principal_time_basis_norm
#check principal_space_basis_norm
#check principal_lorentz_basis_eigen_plus
#check principal_transverse_basis_eigen_minus
#check principalTransversePart_nonneg
#check principal_plus_plane_lorentzian_certificate
#check normalizedClockUnit
#check normalizedClockUnit_eval
#check reeb_direction_unique
#check clock_representatives_differ_by_first_integral
#check common_shift_is_only_endpoint_freedom
#check MaxwellBridgeData.response_positive
#check MaxwellBridgeData.kernel_invisible
#check MaxwellBridgeData.Lambda
#check maxwellBridge_factorization
#check maxwellBridge_Lambda_nonzero
#check maxwellBridge_Lambda_unique
#check maxwellBridge_quotient_finrank_one
#check Sigma_nonneg
#check Sigma_eq_zero_iff
#check kerrChiScalar_pos
#check kerrChiScalar_sq
#check kerrRicciNorm_from_carrier
#check kerrRadialLogGradient_ne_zero_iff
#check hodge_twoform_conformal_iff_four
#check hodge_twoform_four_dimensional
#check maxwell_hodge_exponents_agree
#check conformal_null_hamiltonian_differential
#check linear_sharp_respects_null_scaling
#check conformal_null_hamiltonian_vector_scaling
#check actionBoost_add
#check actionBoost_neg_inverse
#check opticalBoost_add
#check opticalBoost_neg_inverse
#check quartic_logarithmic_derivative
#check clockOmega_eq_dKappa_wedge_dTheta
#check pastEndpointE_empty
#check futureEndpointE_empty
#check pastEndpointE_mono
#check futureEndpointE_mono_of_reverse_inclusion
#check causal_extended_endpoints_mono
#check opposite_null_components_balance_iff_zero
#check sigmaStar_opposite_components
#check kerrClockRate_mul_multiplier
#check kerrClockRate_eq_inv_multiplier
#check carterNumerator_factorization
#check Sigma_hasDerivAt_r
#check kerrChiScalar_hasDerivAt_r
#check kerrLogChi_hasDerivAt_r
#check boostDefect_hasDerivAt
#check boostDefect_derivative_negative
#check restComponent_zero_implies_balance
#check balance_implies_restComponent_zero_of_spacelike
#check balance_iff_restComponent_zero_of_spacelike
#check defect_from_on_shell_equation
#check defect_factorization_identity
#check defect_first_jet_ne_zero
#check character_exchange
#check principalChi_eq_zero_iff
#check rainich_square_nilpotent_at_zero
#check fullJetStabilizer_eq_singleton_of_finite_break
#check mem_fullJetStabilizer_iff
#check iyerWald_boundary_compensation
#check iyerWald_bulk_response
#check characteristic_half_contraction
#check clockOmega_dilation_homogeneous
#check causal_endpoints_branch_independent
#check radar_order_geometry
#check nullCovectorNormSq_boost_invariant
#check nullCovector_nonnull_boost_iff
#check sigmaStar_exchange
#check boostDefect_exchange
#check logarithmic_differential_scale_invariant
#check logarithmic_differential_homothety_invariant
#check pastEndpoint_mono
#check futureEndpoint_mono_of_reverse_inclusion
#check causal_radar_clock_mono
#check maxwellPositiveResponse_pos
#check maxwellPositiveResponse_ne_zero
#check clockPoisson_coordinates
#check principalStress_chi_from_trace
#check carrier_chi_eq_sqrt_ricci_norm
#check RO_ne_zero
#check radialjet_certificate
#check nullCovectorNormSq
#check nullCovectorNormSq_ne_zero_components
#check boost_balance_exists_unique_of_nonnull
#check sigmaStar_balance_of_nonnull
#check kernel_invisible_of_response_extensional
#check alternating_bilinear_zero_on_clock_line
#check clockPotential_increment
#check clockPotential_unique_up_to_constant
#check clockPotential_normalized_flow
#check ExtensionalBridgeData.kernel_invisible
#check ExtensionalBridgeData.Lambda
#check extensionalBridge_factorization
#check extensionalBridge_Lambda_unique
#check extensionalBridge_quotient_finrank_one
#check radar_decomposition_unique
#check frobeniusObstruction_zero_iff
#check principal_endpoint_split
#check clockLiouville_eq_contraction
#check clockLiouville_homogeneous
#check quotientClockCovector
#check quotientClockCovector_pullback
#check quotientClockCovector_ker_eq_bot
#check quotientClockCovector_injective
#check quotientClockCovector_nonzero
#check quotientClockCovector_surjective
#check quotientClockCovectorEquivReal
#check quotient_clock_covector_forced
#check normalized_unit_existsUnique
#check normalizedClockMap_bijective
#check normalizedClockEquiv
#check characteristicCovectorOfKernel
#check characteristicCovectorOfKernel_factorization
#check characteristicCovectorOfKernel_unique
#check involution_eigenspaces_orthogonal
#check actionOpticalMap_injective
#check actionOpticalMap_surjective
#check opticalBoost_TO_injective
#check rapidity_forced_by_normalized_boost
#check localClock_lambda_nonzero
#check localClockQuotientEquivReal
#check localClockQuotient_finrank_one
#check null_pair_closure_iff
#check kerrNewman_mino_clock_forced
#check kerrNewman_vacuum_carrier_vanishes
#check actionBoost_zero
#check actionBoost_fst_hasDerivAt
#check actionBoost_snd_hasDerivAt
#check actionBoost_generated_by_YA
#check opticalBoost_zero
#check opticalBoost_fst_hasDerivAt
#check opticalBoost_snd_hasDerivAt
#check opticalBoost_generated_by_BO
#check scaledResidual_hasDerivAt_zero
#check scaledResidual_full_jet_parity
#check scaledResidual_odd_iteratedDeriv_eq_minus_two_ricci
#check scaledResidual_onShell_eq_sinh
#check scaledResidual_onShell_eq_defect
#check scaledResidual_zero_iff_fixed_point
#check residualLinear_CA
#check residualLinear_DA
#check residualLinear_DA_eq_jet
#check JA_CA
#check JA_DA
#check JA_actionBoost
#check JO_TO
#check JO_RO
#check JO_opticalBoost
#check actionOpticalMap_intertwines_exchange
#check characteristic_range_covector_unique
#check clockQuotientEquivReal
#check clockQuotient_finrank_one
#check delta_eq_zero_iff_one
#check character_rest_iff_zero
#check conformal_factor_forced
#check null_frequency_ratio
#check null_frequency_defect
#check character_ratio_eq_null_frequency_ratio
#check full_relative_rest_equivalence
#check XiGUS_factorization
#check XiMUS_factorization
#check rho_mul_lambda_eq_kappa
#check character_ratio_eq_exp_two
#check relative_coordinate_recovered
#check character_defect_is_tanh
#check solution_preserving_fixed_point_iff
#check defect_eq_zero_iff
#check defect_odd_iteratedDeriv_eq_minus_two_ricci
#check defect_odd_iteratedDeriv_ne_zero
#check defectvelocity_identity
#check chronometric_invariant_chain
#check defect_even_iteratedDeriv_zero
#check defect_odd_iteratedDeriv_carrier
#check defect_full_jet_parity
#check carrierOdd_full_jet_parity
#check carrierEven_full_jet_parity
#check principalChi_pos
#check maxwell_invariants_eq_principalChi_sq
#check maxwell_clock_fourth_power
#check carrier_decomposition_coefficient
#check local_response_ratio_forces_clock
#check energy_density_clock_rate_value
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

/-! Kernel axiom audit. These commands are executable and are intentionally part of the build
transcript: they expose every axiom used by representative end-to-end theorems. -/
#print axioms RelativeRest.scalar_backbone
#print axioms RelativeRest.relationalObservable_gauge_invariant
#print axioms RelativeRest.relationalObservable_deriv
#print axioms RelativeRest.implicit_endpoint_covector_null
#print axioms RelativeRest.primitive_relative_weights_reciprocal_iff_four
#print axioms RelativeRest.scalar_backbone_from_einstein_maxwell
#print axioms RelativeRest.rescaled_solution_preserving_iff
#print axioms RelativeRest.characteristic_half_contraction_from_relative_scaling
#print axioms RelativeRest.principalLocalClockRatio_forced
#print axioms RelativeRest.principalMaxwell_timelike_eigen_from_chi
#print axioms RelativeRest.principalStressFromF_eq_principalStress
#print axioms RelativeRest.principalJetFromF_rainich
#print axioms RelativeRest.principalNormalizedJetFromFApply_eq_involution
#print axioms RelativeRest.principalMaxwell_form_invariant_magnitude
#print axioms RelativeRest.defect_from_on_shell_equation
#print axioms RelativeRest.scaledResidual_first_jet_eq_minus_two_ricci_from_EM
#print axioms RelativeRest.boost_balance_exists_unique_of_nonnull
#print axioms RelativeRest.rapidity_forced_by_normalized_boost
#print axioms RelativeRest.extensionalBridge_Lambda_unique
#print axioms RelativeRest.maxwellBridge_Lambda_unique
#print axioms RelativeRest.reeb_direction_unique
#print axioms RelativeRest.clock_section_reeb_existsUnique
#print axioms RelativeRest.clockQuotientDualEquiv
#print axioms RelativeRest.quotientBilinearForm_unique
#print axioms RelativeRest.causal_extended_endpoints_mono
#print axioms RelativeRest.kerrLogChi_hasDerivAt_r
#print axioms RelativeRest.kerrNewman_mino_clock_forced
#print axioms RelativeRest.kerrNewman_mino_clock_from_principal_EM
#print axioms RelativeRest.kerrMinoClockFromPrincipalEM
#print axioms RelativeRest.kerr_relative_rest_carter_certificate
#print axioms RelativeRest.kerr_regular_first_or_second_radial_jet_resolves
