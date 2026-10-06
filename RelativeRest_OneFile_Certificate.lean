import Mathlib

/-!
# Relative Rest as the Resolution of Frozen Time in Einstein–Maxwell Theory
## One-file Lean certificate of the forced algebraic/uniqueness chain

This file is intentionally adversarial about assumptions.

* Every theorem body below is explicit: there are no `sorry` placeholders or project-local axioms.
* The projective/action-scaling, fixed-point jet, explicit principal Maxwell stress, Rainich
  involution, residual-boost uniqueness, characteristic quotient, one-dimensional clock,
  optical closure, relational-flow algebra, and Kerr–Newman principal-field scalar chain are
  proved in Lean.
* In particular, the strongest Kerr–Newman route reconstructs the Ricci norm, intrinsic clock
  rate, and Mino relation from the explicit principal Maxwell field rather than importing a
  Kerr-specific curvature scalar.
* The Kerr–Newman specialization now also differentiates the Boyer–Lindquist potential,
  reconstructs its coordinate Maxwell field, proves equality with the full Carter orthonormal
  coframe form, derives the metric inverse block and determinant, and proves both the homogeneous
  and source-free Maxwell equations in the regular Boyer–Lindquist chart.  It also derives the
  metric-normalized Carter observer and its carrier-selected rest condition, including the
  higher-jet `r=0` stratum.
* The action side is now pushed back to explicit Einstein-Hilbert/Maxwell density pieces
  and a reciprocal Lagrangian object.  Every linear covariant descendant is proved to inherit
  the same characters, so the odd presymplectic sector and the `-2` constraint jet are no
  longer independent scaling inputs.  A single Lagrangian-level Iyer-Wald operator identity
  then uniquely fixes the compensated current and connects it to the explicit Maxwell stress,
  characteristic covector, one-dimensional quotient, and normalized principal clock line.
* What is not yet reconstructed from first principles is concentrated in the remaining
  manifold-level differential-geometric infrastructure: the genuine tensor/differential-form
  variation theorem for the Einstein-Maxwell Lagrangian (including construction of its
  symplectic potential/Noether charge and proof of the operator-level Iyer-Wald identity),
  the remaining stationary `(t,phi)` Kerr-Newman Ricci block, and global smooth
  Synge-world-function endpoint existence across caustics.  Once those geometric inputs are
  available, their algebraic, quotient, transport, clock, optical, and Kerr consequences are
  already forced by the theorems below.

Consequently this file is a kernel-oriented logical certificate of the manuscript's forced
algebraic and quotient structure while keeping the remaining geometric boundary visible.
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

/-! ### Explicit reciprocal two-sector action -/

/-- Common-character-removed two-sector action along the relative coordinate. -/
def relativeActionValue
    (SG SM s : ℝ) : ℝ :=
  Real.exp (-s) * SG + Real.exp s * SM

/-- Exchange of gravity/Maxwell sectors is exactly reversal of the relative coordinate. -/
theorem relativeActionValue_exchange
    (SG SM s : ℝ) :
    relativeActionValue SM SG (-s) =
      relativeActionValue SG SM s := by
  unfold relativeActionValue
  ring

/-- The normal derivative of the reciprocal action is the exchange-odd sector difference. -/
theorem relativeActionValue_hasDerivAt
    (SG SM s : ℝ) :
    HasDerivAt
      (relativeActionValue SG SM)
      (-Real.exp (-s) * SG + Real.exp s * SM) s := by
  have hneg : HasDerivAt (fun x : ℝ => -x) (-1) s :=
    (hasDerivAt_id s).neg
  have hG :
      HasDerivAt
        (fun x : ℝ => Real.exp (-x) * SG)
        (-Real.exp (-s) * SG) s := by
    have he := (Real.hasDerivAt_exp (-s)).comp s hneg
    convert he.mul_const SG using 1 <;> ring
  have hM :
      HasDerivAt
        (fun x : ℝ => Real.exp x * SM)
        (Real.exp s * SM) s :=
    (Real.hasDerivAt_exp s).mul_const SM
  simpa [relativeActionValue] using hG.add hM

/-- At the relative fixed point the action normal is exactly `SM-SG`. -/
theorem relativeActionValue_deriv_zero
    (SG SM : ℝ) :
    deriv (relativeActionValue SG SM) 0 = SM - SG := by
  rw [(relativeActionValue_hasDerivAt SG SM 0).deriv]
  simp
  ring

/-- On the solution-preserving diagonal the relative action is exchange-even. -/
theorem relativeActionValue_diagonal
    (S s : ℝ) :
    relativeActionValue S S s =
      2 * S * Real.cosh s := by
  unfold relativeActionValue
  rw [Real.cosh_eq]
  ring

/-- Consequently its first normal derivative vanishes at relative rest. -/
theorem relativeActionValue_diagonal_deriv_zero
    (S : ℝ) :
    deriv (relativeActionValue S S) 0 = 0 := by
  rw [relativeActionValue_deriv_zero]
  ring

/-- The corresponding sector difference is the odd companion and survives at first order. -/
def relativeActionDefect
    (S s : ℝ) : ℝ :=
  Real.exp (-s) * S - Real.exp s * S

@[simp] theorem relativeActionDefect_zero
    (S : ℝ) :
    relativeActionDefect S 0 = 0 := by
  simp [relativeActionDefect]

theorem relativeActionDefect_hasDerivAt_zero
    (S : ℝ) :
    HasDerivAt (relativeActionDefect S) (-2 * S) 0 := by
  have hfun :
      relativeActionDefect S =
        fun s : ℝ => (-2 * S) * Real.sinh s := by
    funext s
    unfold relativeActionDefect
    rw [Real.sinh_eq]
    ring
  rw [hfun]
  simpa using (Real.hasDerivAt_sinh 0).const_mul (-2 * S)

/-- The action pair therefore has the same fixed-value/first-jet architecture as the
field-equation carrier: even value, vanishing odd value, surviving odd first jet. -/
theorem relativeAction_fixed_point_jet
    (S : ℝ) :
    deriv (relativeActionValue S S) 0 = 0 ∧
    relativeActionDefect S 0 = 0 ∧
    deriv (relativeActionDefect S) 0 = -2 * S := by
  refine ⟨relativeActionValue_diagonal_deriv_zero S,
    relativeActionDefect_zero S, ?_⟩
  exact (relativeActionDefect_hasDerivAt_zero S).deriv

/-- The normalized action defect/value ratio is exactly the rapidity coordinate. -/
theorem relativeAction_defect_ratio
    (S s : ℝ) (hS : S ≠ 0) :
    - relativeActionDefect S s /
        relativeActionValue S S s =
      Real.tanh s := by
  rw [relativeActionValue_diagonal]
  unfold relativeActionDefect
  rw [Real.tanh_eq_sinh_div_cosh,
    Real.sinh_eq, Real.cosh_eq]
  have hc : Real.cosh s ≠ 0 := ne_of_gt (Real.cosh_pos s)
  field_simp [hS, hc]
  ring

/-! ### Einstein-Maxwell Lagrangian origin of the reciprocal character -/

/-- Einstein-Hilbert density coefficient for `(16π)⁻¹ R ε_g`. -/
def einsteinHilbertLagrangianDensity
    (volumeCoeff scalarR : ℝ) : ℝ :=
  (1 / (16 * Real.pi)) * volumeCoeff * scalarR

/-- Maxwell density coefficient for `-(16π)⁻¹ F² ε_g`. -/
def maxwellLagrangianDensity
    (volumeCoeff Fsq : ℝ) : ℝ :=
  -(1 / (16 * Real.pi)) * volumeCoeff * Fsq

/-- Pointwise Einstein-Maxwell Lagrangian density in the manuscript normalization. -/
def einsteinMaxwellLagrangianDensity
    (volumeCoeff scalarR Fsq : ℝ) : ℝ :=
  (1 / (16 * Real.pi)) * volumeCoeff * (scalarR - Fsq)

theorem einsteinMaxwellLagrangianDensity_decomposition
    (volumeCoeff scalarR Fsq : ℝ) :
    einsteinMaxwellLagrangianDensity volumeCoeff scalarR Fsq =
      einsteinHilbertLagrangianDensity volumeCoeff scalarR +
        maxwellLagrangianDensity volumeCoeff Fsq := by
  unfold einsteinMaxwellLagrangianDensity
    einsteinHilbertLagrangianDensity maxwellLagrangianDensity
  ring

/-- Literal directional first variation of the displayed Einstein-Maxwell density.
This is the pointwise algebraic part of the action variation; the curvature boundary
decomposition is handled separately by the covariant first-variation interface below. -/
theorem einsteinMaxwellLagrangianDensity_hasDerivAt_line_zero
    (volumeCoeff scalarR Fsq dVolume dR dFsq : ℝ) :
    HasDerivAt
      (fun s : ℝ => einsteinMaxwellLagrangianDensity
        (volumeCoeff + s * dVolume)
        (scalarR + s * dR)
        (Fsq + s * dFsq))
      ((1 / (16 * Real.pi)) *
        (dVolume * (scalarR - Fsq) +
          volumeCoeff * (dR - dFsq))) 0 := by
  have hV :
      HasDerivAt (fun s : ℝ => volumeCoeff + s * dVolume)
        dVolume 0 := by
    convert (hasDerivAt_const 0 volumeCoeff).add
      ((hasDerivAt_id 0).mul_const dVolume) using 1 <;> ring
  have hRF :
      HasDerivAt
        (fun s : ℝ => (scalarR + s * dR) - (Fsq + s * dFsq))
        (dR - dFsq) 0 := by
    convert ((hasDerivAt_const 0 scalarR).add
      ((hasDerivAt_id 0).mul_const dR)).sub
      ((hasDerivAt_const 0 Fsq).add
        ((hasDerivAt_id 0).mul_const dFsq)) using 1 <;> ring
  have h := (hV.mul hRF).const_mul (1 / (16 * Real.pi))
  unfold einsteinMaxwellLagrangianDensity
  convert h using 1 <;> ring

/-- The derivative of the displayed density is therefore fixed uniquely by its three
primitive scalar variations; no extra density-level normalization survives. -/
theorem einsteinMaxwellLagrangianDensity_line_deriv_zero
    (volumeCoeff scalarR Fsq dVolume dR dFsq : ℝ) :
    deriv
      (fun s : ℝ => einsteinMaxwellLagrangianDensity
        (volumeCoeff + s * dVolume)
        (scalarR + s * dR)
        (Fsq + s * dFsq)) 0 =
      (1 / (16 * Real.pi)) *
        (dVolume * (scalarR - Fsq) +
          volumeCoeff * (dR - dFsq)) :=
  (einsteinMaxwellLagrangianDensity_hasDerivAt_line_zero
    volumeCoeff scalarR Fsq dVolume dR dFsq).deriv

section LagrangianFunctoriality

variable {L O : Type*}
  [AddCommGroup L] [Module ℝ L]
  [AddCommGroup O] [Module ℝ O]

/-- Reciprocal Einstein-Maxwell Lagrangian family after removal of the common character. -/
def reciprocalLagrangian
    (LG LM : L) (s : ℝ) : L :=
  Real.exp (-s) • LG + Real.exp s • LM

theorem reciprocalLagrangian_exchange
    (LG LM : L) (s : ℝ) :
    reciprocalLagrangian LM LG (-s) =
      reciprocalLagrangian LG LM s := by
  simp [reciprocalLagrangian]
  module

/-- Fixed-point normal jet of the reciprocal Lagrangian family. -/
def reciprocalLagrangianNormalJet
    (LG LM : L) : L :=
  -LG + LM

/-- Every linear covariant descendant inherits the same reciprocal characters. -/
theorem linearDescendant_reciprocal
    (D : L →ₗ[ℝ] O) (LG LM : L) (s : ℝ) :
    D (reciprocalLagrangian LG LM s) =
      Real.exp (-s) • D LG + Real.exp s • D LM := by
  simp [reciprocalLagrangian]

/-- Taking the fixed-point normal jet commutes with every linear Lagrangian descendant. -/
theorem linearDescendant_normalJet
    (D : L →ₗ[ℝ] O) (LG LM : L) :
    D (reciprocalLagrangianNormalJet LG LM) =
      -D LG + D LM := by
  simp [reciprocalLagrangianNormalJet]

/-- Opposite sector values force the universal `-2` relative jet. -/
theorem linearDescendant_normalJet_of_opposite
    (D : L →ₗ[ℝ] O) (LG LM : L) (ell : O)
    (hG : D LG = ell)
    (hM : D LM = -ell) :
    D (reciprocalLagrangianNormalJet LG LM) = (-2 : ℝ) • ell := by
  rw [linearDescendant_normalJet D LG LM, hG, hM]
  module

/-- Scalar descendants admit the literal derivative form of the normal-jet theorem. -/
theorem linearDescendant_reciprocal_hasDerivAt_zero
    (D : L →ₗ[ℝ] ℝ) (LG LM : L) :
    HasDerivAt
      (fun s : ℝ => D (reciprocalLagrangian LG LM s))
      (-D LG + D LM) 0 := by
  have hformula :
      (fun s : ℝ => D (reciprocalLagrangian LG LM s)) =
        (fun s : ℝ => Real.exp (-s) * D LG + Real.exp s * D LM) := by
    funext s
    rw [linearDescendant_reciprocal D LG LM s]
    simp [smul_eq_mul]
  rw [hformula]
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) 0 :=
    (hasDerivAt_id 0).neg
  have hGexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-1) 0 := by
    simpa using (Real.hasDerivAt_exp 0).comp 0 hneg
  have hG := hGexp.mul_const (D LG)
  have hM := (Real.hasDerivAt_exp 0).mul_const (D LM)
  convert hG.add hM using 1 <;> simp <;> ring

end LagrangianFunctoriality

/-- Four-dimensional sector scaling factors through the common character and the
reciprocal Lagrangian family. -/
def scaledEinsteinMaxwellSectorValue
    (u s SG SM : ℝ) : ℝ :=
  XiGUS u s * SG + XiMUS u s * SM

theorem scaledEinsteinMaxwellSectorValue_factorization
    (u s SG SM : ℝ) :
    scaledEinsteinMaxwellSectorValue u s SG SM =
      kappaUS u * relativeActionValue SG SM s := by
  unfold scaledEinsteinMaxwellSectorValue relativeActionValue
  rw [XiGUS_factorization, XiMUS_factorization]
  ring

theorem relativeActionValue_eq_reciprocalLagrangian
    (SG SM s : ℝ) :
    relativeActionValue SG SM s =
      reciprocalLagrangian SG SM s := by
  simp [relativeActionValue, reciprocalLagrangian, smul_eq_mul]

theorem relativeActionDefect_eq_reciprocalLagrangian
    (S s : ℝ) :
    relativeActionDefect S s =
      reciprocalLagrangian S (-S) s := by
  simp [relativeActionDefect, reciprocalLagrangian, smul_eq_mul]
  ring

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

/-! ### Maxwell metric first variation from the Einstein-Maxwell Lagrangian -/

/-- Covariant quadratic contraction `F_{ic} F_j{}^c` in the principal frame. -/
def principalMaxwellCovariantContraction
    (E B : ℝ) (i j : Fin 4) : ℝ :=
  ∑ c : Fin 4,
    principalMaxwellF E B i c *
      principalMetricSign c *
      principalMaxwellF E B j c

/-- Covariant metric coefficient in the orthonormal principal frame. -/
def principalMetricCov (i j : Fin 4) : ℝ :=
  if i = j then principalMetricSign i else 0

/-- The inverse-metric variation of `F^2` contributes the factor two fixed by the
two inverse metrics in the Maxwell Lagrangian. -/
def principalMaxwellInverseMetricVariationCoeff
    (E B : ℝ) (i j : Fin 4) : ℝ :=
  -(1 / (8 * Real.pi)) *
    principalMaxwellCovariantContraction E B i j

/-- The volume-density variation contributes `+(32π)⁻¹ g_ij F²`. -/
def principalMaxwellVolumeVariationCoeff
    (E B : ℝ) (i j : Fin 4) : ℝ :=
  (1 / (32 * Real.pi)) *
    principalMetricCov i j * principalMaxwellFsq E B

/-- Total algebraic coefficient of `δg^{ij}` in the Maxwell Lagrangian density,
after factoring out the background volume density. -/
def principalMaxwellMetricVariationCoeff
    (E B : ℝ) (i j : Fin 4) : ℝ :=
  principalMaxwellInverseMetricVariationCoeff E B i j +
    principalMaxwellVolumeVariationCoeff E B i j

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

/-- Covariant stress obtained by lowering the first index of the mixed stress. -/
def principalStressCovFromF
    (E B : ℝ) (i j : Fin 4) : ℝ :=
  principalMetricSign i * principalStressFromF E B i j

/-- The two primitive metric-variation contributions combine to exactly
`-1/2 T_ij[F]`.  Thus the stress normalization and the trace subtraction are
forced by the Maxwell Lagrangian normalization. -/
theorem principalMaxwellMetricVariationCoeff_eq_neg_half_stress
    (E B : ℝ) (i j : Fin 4) :
    principalMaxwellMetricVariationCoeff E B i j =
      (-1 / 2 : ℝ) * principalStressCovFromF E B i j := by
  fin_cases i <;> fin_cases j <;>
    simp [principalMaxwellMetricVariationCoeff,
      principalMaxwellInverseMetricVariationCoeff,
      principalMaxwellVolumeVariationCoeff,
      principalMaxwellCovariantContraction, principalMetricCov,
      principalStressCovFromF, principalStressFromF,
      principalMetricSign, principalMaxwellF,
      principalMaxwellFsq_eq_maxwellI, maxwellI] <;>
    field_simp [ne_of_gt Real.pi_pos] <;>
    ring

/-- Einstein-Hilbert metric-variation coefficient in mixed-index form after
lowering the first index with the principal metric. -/
def principalEinsteinHilbertMetricVariationCoeff
    (Gmixed : Fin 4 → Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  (1 / (16 * Real.pi)) *
    principalMetricSign i * Gmixed i j

/-- Total Einstein-Maxwell metric Euler-Lagrange coefficient for an arbitrary
candidate mixed Einstein tensor and the explicit principal Maxwell field. -/
def principalEinsteinMaxwellMetricVariationCoeff
    (Gmixed : Fin 4 → Fin 4 → ℝ)
    (E B : ℝ) (i j : Fin 4) : ℝ :=
  principalEinsteinHilbertMetricVariationCoeff Gmixed i j +
    principalMaxwellMetricVariationCoeff E B i j

/-- The total metric first-variation coefficient factors by the Einstein-Maxwell
residual `G^i_j - 8π T^i_j`. -/
theorem principalEinsteinMaxwellMetricVariationCoeff_factor
    (Gmixed : Fin 4 → Fin 4 → ℝ)
    (E B : ℝ) (i j : Fin 4) :
    principalEinsteinMaxwellMetricVariationCoeff Gmixed E B i j =
      (principalMetricSign i / (16 * Real.pi)) *
        (Gmixed i j - 8 * Real.pi * principalStressFromF E B i j) := by
  rw [principalEinsteinMaxwellMetricVariationCoeff,
    principalMaxwellMetricVariationCoeff_eq_neg_half_stress]
  unfold principalEinsteinHilbertMetricVariationCoeff
    principalStressCovFromF
  field_simp [ne_of_gt Real.pi_pos]
  ring

/-- Principal-frame metric signs are never zero. -/
theorem principalMetricSign_ne_zero (i : Fin 4) :
    principalMetricSign i ≠ 0 := by
  fin_cases i <;> simp [principalMetricSign]

/-- Stationarity of the Einstein-Maxwell metric variation is componentwise
equivalent to the Einstein equation with the explicit Maxwell stress. -/
theorem principalEinsteinMaxwellMetricVariationCoeff_eq_zero_iff
    (Gmixed : Fin 4 → Fin 4 → ℝ)
    (E B : ℝ) (i j : Fin 4) :
    principalEinsteinMaxwellMetricVariationCoeff Gmixed E B i j = 0 ↔
      Gmixed i j = 8 * Real.pi * principalStressFromF E B i j := by
  rw [principalEinsteinMaxwellMetricVariationCoeff_factor]
  have hc : principalMetricSign i / (16 * Real.pi) ≠ 0 := by
    exact div_ne_zero (principalMetricSign_ne_zero i)
      (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))
  constructor
  · intro h
    have hres :
        Gmixed i j - 8 * Real.pi * principalStressFromF E B i j = 0 := by
      exact (mul_eq_zero.mp h).resolve_left hc
    linarith
  · intro h
    rw [h]
    ring

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

/-- Principal energy density is quadratic under common Maxwell-field amplitude scaling. -/
theorem principalFieldEnergyDensity_scale
    (c E B : ℝ) :
    principalFieldEnergyDensity (c * E) (c * B) =
      c^2 * principalFieldEnergyDensity E B := by
  unfold principalFieldEnergyDensity
  ring

/-- The canonical mixed principal stress is linear in its scalar eigenvalue. -/
theorem principalStress_scale
    (c u : ℝ) (i j : Fin 4) :
    principalStress (c * u) i j =
      c * principalStress u i j := by
  fin_cases i <;> fin_cases j <;>
    simp [principalStress] <;> ring

/-- Therefore Maxwell stress is quadratically forced by field amplitude:
`T[cF]=c²T[F]`. -/
theorem principalStressFromF_scale
    (c E B : ℝ) (i j : Fin 4) :
    principalStressFromF (c * E) (c * B) i j =
      c^2 * principalStressFromF E B i j := by
  rw [principalStressFromF_eq_principalStress,
    principalStressFromF_eq_principalStress,
    principalFieldEnergyDensity_scale,
    principalStress_scale]

/-- The relative Maxwell character is therefore exactly `e^{2s}` at stress level. -/
theorem principalStressFromF_exp_scale
    (s E B : ℝ) (i j : Fin 4) :
    principalStressFromF (Real.exp s * E) (Real.exp s * B) i j =
      Real.exp (2 * s) * principalStressFromF E B i j := by
  rw [principalStressFromF_scale]
  rw [show (Real.exp s)^2 = Real.exp (2 * s) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]

/-- The stress eigenvalue scale is exactly `χ/(16π)` because `χ=2(E²+B²)`. -/
theorem principalFieldEnergyDensity_eq_chi
    (E B : ℝ) :
    principalFieldEnergyDensity E B =
      principalChi E B / (16 * Real.pi) := by
  unfold principalFieldEnergyDensity principalChi
  field_simp [ne_of_gt Real.pi_pos]
  ring


/-- A nonzero principal Maxwell field has strictly positive energy density. -/
theorem principalFieldEnergyDensity_pos_of_nonzero
    (E B : ℝ) (hfield : E ≠ 0 ∨ B ≠ 0) :
    0 < principalFieldEnergyDensity E B := by
  rw [principalFieldEnergyDensity_eq_chi]
  exact div_pos
    (principalChi_pos E B hfield)
    (mul_pos (by norm_num) Real.pi_pos)

/-- The explicit timelike mixed stress component is the negative energy density. -/
theorem principalStressFromF_00
    (E B : ℝ) :
    principalStressFromF E B 0 0 =
      - principalFieldEnergyDensity E B := by
  rw [principalStressFromF_eq_principalStress]
  simp [principalStress]

/-- Componentwise common-character-removed Einstein-Maxwell residual for the explicit field. -/
def principalScaledResidualFromF
    (E B : ℝ) (i j : Fin 4) (s : ℝ) : ℝ :=
  8 * Real.pi * principalStressFromF E B i j -
    8 * Real.pi * Real.exp (2 * s) *
      principalStressFromF E B i j

/-- Every explicit field component lies on the relative fixed point at `s=0`. -/
@[simp] theorem principalScaledResidualFromF_zero
    (E B : ℝ) (i j : Fin 4) :
    principalScaledResidualFromF E B i j 0 = 0 := by
  simp [principalScaledResidualFromF]

/-- On the nonzero Maxwell sector the timelike Einstein-Maxwell component preserves the
field equation under relative scaling if and only if `s=0`. -/
theorem principalField_solution_preserving_iff
    (u s E B : ℝ)
    (hfield : E ≠ 0 ∨ B ≠ 0) :
    (8 * Real.pi * principalFieldEnergyDensity E B =
      8 * Real.pi *
        maxwellStressScaleFactor (rhoUS u s) (lambdaUS u s) *
        principalFieldEnergyDensity E B) ↔
      s = 0 := by
  exact rescaled_solution_preserving_iff
    u s (principalFieldEnergyDensity E B)
    (ne_of_gt (principalFieldEnergyDensity_pos_of_nonzero E B hfield))

/-- Equivalently the actual `00` residual has a unique zero at the relative fixed point. -/
theorem principalScaledResidualFromF_00_zero_iff
    (E B s : ℝ)
    (hfield : E ≠ 0 ∨ B ≠ 0) :
    principalScaledResidualFromF E B 0 0 s = 0 ↔ s = 0 := by
  unfold principalScaledResidualFromF
  rw [principalStressFromF_00]
  have hε :
      principalFieldEnergyDensity E B ≠ 0 :=
    ne_of_gt (principalFieldEnergyDensity_pos_of_nonzero E B hfield)
  have hcoef :
      8 * Real.pi * (-principalFieldEnergyDensity E B) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))
      (neg_ne_zero.mpr hε)
  constructor
  · intro h
    have hfact :
        (8 * Real.pi * (-principalFieldEnergyDensity E B)) *
          (1 - Real.exp (2 * s)) = 0 := by
      calc
        (8 * Real.pi * (-principalFieldEnergyDensity E B)) *
            (1 - Real.exp (2 * s))
            =
          8 * Real.pi * (-principalFieldEnergyDensity E B) -
            8 * Real.pi * Real.exp (2 * s) *
              (-principalFieldEnergyDensity E B) := by ring
        _ = 0 := h
    have hscale0 : 1 - Real.exp (2 * s) = 0 :=
      (mul_eq_zero.mp hfact).resolve_left hcoef
    have hscale : Real.exp (2 * s) = 1 := by linarith
    exact (exp_two_eq_one_iff s).mp hscale
  · rintro rfl
    simp


/-- Overall Maxwell-field orientation reversal does not change the principal energy density. -/
@[simp] theorem principalFieldEnergyDensity_neg
    (E B : ℝ) :
    principalFieldEnergyDensity (-E) (-B) =
      principalFieldEnergyDensity E B := by
  unfold principalFieldEnergyDensity
  ring

/-- Nor does it change the Rainich carrier magnitude. -/
@[simp] theorem principalChi_neg (E B : ℝ) :
    principalChi (-E) (-B) = principalChi E B := by
  unfold principalChi
  ring

/-- The Maxwell stress tensor is quadratic, hence invariant under the overall sign
change induced by the Carter coframe orientation. -/
theorem principalStressFromF_neg
    (E B : ℝ) (i j : Fin 4) :
    principalStressFromF (-E) (-B) i j =
      principalStressFromF E B i j := by
  rw [principalStressFromF_eq_principalStress,
    principalStressFromF_eq_principalStress,
    principalFieldEnergyDensity_neg]

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
  simp [principalStress]
  ring

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


/-- The first normal derivative of the explicit residual is exactly the fixed-point jet
`J[F]=-16πT[F]`. -/
theorem principalScaledResidualFromF_hasDerivAt_zero
    (E B : ℝ) (i j : Fin 4) :
    HasDerivAt
      (principalScaledResidualFromF E B i j)
      (principalJetFromF E B i j) 0 := by
  have hexp :
      HasDerivAt (fun s : ℝ => Real.exp (2 * s)) 2 0 := by
    have hlin : HasDerivAt (fun s : ℝ => 2 * s) 2 0 :=
      (hasDerivAt_id 0).const_mul 2
    simpa using (Real.hasDerivAt_exp 0).comp 0 hlin
  have hscaled :=
    hexp.const_mul
      (8 * Real.pi * principalStressFromF E B i j)
  have hconst :
      HasDerivAt
        (fun _ : ℝ =>
          8 * Real.pi * principalStressFromF E B i j)
        0 0 :=
    hasDerivAt_const 0 _
  unfold principalScaledResidualFromF principalJetFromF
  convert hconst.sub hscaled using 1 <;> ring

/-- Derivative form of the explicit fixed-point jet identity. -/
theorem principalScaledResidualFromF_deriv_zero
    (E B : ℝ) (i j : Fin 4) :
    deriv (principalScaledResidualFromF E B i j) 0 =
      principalJetFromF E B i j :=
  (principalScaledResidualFromF_hasDerivAt_zero E B i j).deriv

/-! ### Relative carrier as an Einstein-Maxwell action Euler jet -/

/-- Mixed Einstein tensor selected by the unscaled Einstein-Maxwell metric
Euler-Lagrange equation for the explicit principal Maxwell field. -/
def principalOnShellEinsteinFromF
    (E B : ℝ) (i j : Fin 4) : ℝ :=
  8 * Real.pi * principalStressFromF E B i j

/-- Metric Euler-Lagrange coefficient of the same gravity tensor against the
relatively scaled Maxwell field `F_s=e^s F`. -/
def principalScaledMetricEulerCoeffFromAction
    (E B : ℝ) (i j : Fin 4) (s : ℝ) : ℝ :=
  principalEinsteinMaxwellMetricVariationCoeff
    (principalOnShellEinsteinFromF E B)
    (Real.exp s * E) (Real.exp s * B) i j

/-- At relative rest the scaled action Euler coefficient vanishes exactly. -/
@[simp] theorem principalScaledMetricEulerCoeffFromAction_zero
    (E B : ℝ) (i j : Fin 4) :
    principalScaledMetricEulerCoeffFromAction E B i j 0 = 0 := by
  unfold principalScaledMetricEulerCoeffFromAction
    principalOnShellEinsteinFromF
  rw [principalEinsteinMaxwellMetricVariationCoeff_eq_zero_iff]
  simp

/-- The action-derived metric Euler coefficient is exactly the isolated
Einstein-Maxwell relative residual times the nonzero action prefactor. -/
theorem principalScaledMetricEulerCoeffFromAction_eq_residual
    (E B : ℝ) (i j : Fin 4) (s : ℝ) :
    principalScaledMetricEulerCoeffFromAction E B i j s =
      (principalMetricSign i / (16 * Real.pi)) *
        principalScaledResidualFromF E B i j s := by
  unfold principalScaledMetricEulerCoeffFromAction
    principalOnShellEinsteinFromF
  rw [principalEinsteinMaxwellMetricVariationCoeff_factor,
    principalStressFromF_exp_scale]
  unfold principalScaledResidualFromF
  ring

/-- Thus the action Euler equation has the same unique nonzero-field fixed point,
rather than merely sharing it by analogy. -/
theorem principalScaledMetricEulerCoeffFromAction_00_zero_iff
    (E B s : ℝ)
    (hfield : E ≠ 0 ∨ B ≠ 0) :
    principalScaledMetricEulerCoeffFromAction E B 0 0 s = 0 ↔
      s = 0 := by
  rw [principalScaledMetricEulerCoeffFromAction_eq_residual]
  have hc : principalMetricSign (0 : Fin 4) / (16 * Real.pi) ≠ 0 := by
    exact div_ne_zero (principalMetricSign_ne_zero 0)
      (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))
  constructor
  · intro h
    have hr : principalScaledResidualFromF E B 0 0 s = 0 :=
      (mul_eq_zero.mp h).resolve_left hc
    exact (principalScaledResidualFromF_00_zero_iff E B s hfield).mp hr
  · intro hs
    rw [hs]
    simp

/-- The first normal derivative of the action-derived Euler coefficient is
the fixed-point carrier jet times the action normalization prefactor. -/
theorem principalScaledMetricEulerCoeffFromAction_hasDerivAt_zero
    (E B : ℝ) (i j : Fin 4) :
    HasDerivAt
      (principalScaledMetricEulerCoeffFromAction E B i j)
      ((principalMetricSign i / (16 * Real.pi)) *
        principalJetFromF E B i j) 0 := by
  have hres := principalScaledResidualFromF_hasDerivAt_zero E B i j
  have hmul := hres.const_mul
    (principalMetricSign i / (16 * Real.pi))
  have heq :
      principalScaledMetricEulerCoeffFromAction E B i j =
        fun s : ℝ =>
          (principalMetricSign i / (16 * Real.pi)) *
            principalScaledResidualFromF E B i j s := by
    funext s
    exact principalScaledMetricEulerCoeffFromAction_eq_residual E B i j s
  rw [heq]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- The carrier jet is therefore uniquely recoverable from the metric Euler jet;
the conversion factor is fixed entirely by the Einstein-Hilbert normalization. -/
theorem principalJetFromF_forced_from_actionEulerJet
    (E B : ℝ) (i j : Fin 4) :
    principalJetFromF E B i j =
      (16 * Real.pi / principalMetricSign i) *
        deriv (principalScaledMetricEulerCoeffFromAction E B i j) 0 := by
  rw [(principalScaledMetricEulerCoeffFromAction_hasDerivAt_zero
    E B i j).deriv]
  have hi := principalMetricSign_ne_zero i
  field_simp [hi, ne_of_gt Real.pi_pos]
  ring



/-- Consequently the fixed-point carrier jet is orientation-independent under
the overall Maxwell-field sign reversal induced by coframe orientation. -/
theorem principalJetFromF_neg
    (E B : ℝ) (i j : Fin 4) :
    principalJetFromF (-E) (-B) i j =
      principalJetFromF E B i j := by
  unfold principalJetFromF
  rw [principalStressFromF_neg]

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

/-- Invariant squared trace of the actual field-derived fixed-point jet. -/
def principalJetFromFTraceSq (E B : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ k : Fin 4,
    principalJetFromF E B i k * principalJetFromF E B k i

/-- The actual jet has squared trace `4χ²`. -/
theorem principalJetFromF_trace_sq (E B : ℝ) :
    principalJetFromFTraceSq E B =
      4 * (principalChi E B)^2 := by
  unfold principalJetFromFTraceSq
  simp_rw [principalJetFromF_eq_neg_principalStress]
  have h :=
    principalStress_trace_sq (principalChi E B)
  unfold principalStressTraceSq at h
  simpa only [neg_mul_neg] using h

/-- Hence the invariant definition
`χ=(1/2)sqrt(tr J²)` recovers the field-derived Maxwell carrier exactly. -/
theorem principalJetFromF_chi_from_trace (E B : ℝ) :
    (1 / 2 : ℝ) *
        Real.sqrt (principalJetFromFTraceSq E B) =
      principalChi E B := by
  rw [principalJetFromF_trace_sq]
  have hχ : 0 ≤ principalChi E B :=
    principalChi_nonneg E B
  have hsq :
      4 * (principalChi E B)^2 =
        (2 * principalChi E B)^2 := by ring
  rw [hsq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 2 * principalChi E B)]
  ring

/-- Ricci endomorphism reconstructed pointwise from the field-equation identity
`J=-2R`. -/
def principalRicciFromF (E B : ℝ) (i j : Fin 4) : ℝ :=
  (-1 / 2 : ℝ) * principalJetFromF E B i j

/-- Squared Ricci norm of the reconstructed principal Ricci endomorphism. -/
def principalRicciFromFTraceSq (E B : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ k : Fin 4,
    principalRicciFromF E B i k *
      principalRicciFromF E B k i

/-- Independent Einstein-equation reconstruction of the mixed Ricci tensor from the
explicit Maxwell stress, using the trace-free four-dimensional reduction
`R^a_b = 8π T^a_b`. -/
def principalRicciFromEinsteinF
    (E B : ℝ) (i j : Fin 4) : ℝ :=
  8 * Real.pi * principalStressFromF E B i j

/-- The fixed-point-jet and Einstein-equation reconstructions of Ricci coincide exactly. -/
theorem principalRicciFromF_eq_Einstein
    (E B : ℝ) (i j : Fin 4) :
    principalRicciFromF E B i j =
      principalRicciFromEinsteinF E B i j := by
  unfold principalRicciFromF principalRicciFromEinsteinF principalJetFromF
  ring

/-- Scalar curvature of the Einstein-reconstructed principal Ricci endomorphism. -/
def principalRicciFromEinsteinTrace
    (E B : ℝ) : ℝ :=
  ∑ i : Fin 4, principalRicciFromEinsteinF E B i i

/-- The explicit Maxwell field forces vanishing scalar curvature. -/
theorem principalRicciFromEinstein_trace_zero
    (E B : ℝ) :
    principalRicciFromEinsteinTrace E B = 0 := by
  unfold principalRicciFromEinsteinTrace principalRicciFromEinsteinF
  simp_rw [principalStressFromF_eq_principalStress]
  simp [principalStress, principalFieldEnergyDensity]
  ring

/-- Mixed Einstein tensor reconstructed from the Einstein-derived Ricci tensor. -/
def principalEinsteinTensorFromF
    (E B : ℝ) (i j : Fin 4) : ℝ :=
  principalRicciFromEinsteinF E B i j -
    (1 / 2 : ℝ) *
      (if i = j then 1 else 0) *
      principalRicciFromEinsteinTrace E B

/-- The explicit principal field satisfies the algebraic Einstein equation identically:
`G^a_b = 8π T^a_b`. -/
theorem principalEinsteinTensorFromF_eq_stress
    (E B : ℝ) (i j : Fin 4) :
    principalEinsteinTensorFromF E B i j =
      8 * Real.pi * principalStressFromF E B i j := by
  rw [principalEinsteinTensorFromF,
    principalRicciFromEinstein_trace_zero]
  simp [principalRicciFromEinsteinF]

/-- Consequently the fixed-point jet-curvature identity is derived from the explicit
Einstein-Maxwell field equation rather than inserted into the Ricci definition. -/
theorem principalJetFromF_eq_minus_two_EinsteinRicci
    (E B : ℝ) (i j : Fin 4) :
    principalJetFromF E B i j =
      -2 * principalRicciFromEinsteinF E B i j := by
  rw [← principalRicciFromF_eq_Einstein]
  unfold principalRicciFromF
  ring

/-- The field-derived Ricci norm is exactly `χ²`. -/
theorem principalRicciFromF_trace_sq (E B : ℝ) :
    principalRicciFromFTraceSq E B =
      (principalChi E B)^2 := by
  unfold principalRicciFromFTraceSq principalRicciFromF
  have hJ := principalJetFromF_trace_sq E B
  unfold principalJetFromFTraceSq at hJ
  calc
    (∑ i : Fin 4, ∑ k : Fin 4,
      ((-1 / 2 : ℝ) * principalJetFromF E B i k) *
        ((-1 / 2 : ℝ) * principalJetFromF E B k i))
        =
      (∑ i : Fin 4, ∑ k : Fin 4,
        (1 / 4 : ℝ) *
          (principalJetFromF E B i k *
            principalJetFromF E B k i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro k hk
              ring
    _ =
      (1 / 4 : ℝ) *
        (∑ i : Fin 4, ∑ k : Fin 4,
          principalJetFromF E B i k *
            principalJetFromF E B k i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
    _ = (1 / 4 : ℝ) *
        (4 * (principalChi E B)^2) := by rw [hJ]
    _ = (principalChi E B)^2 := by ring

/-- Therefore the two invariant definitions in `chiS` agree directly for the explicit field:
`(1/2)sqrt(tr J²)=sqrt(tr R²)=χ`. -/
theorem principalField_chiS_invariants (E B : ℝ) :
    (1 / 2 : ℝ) *
        Real.sqrt (principalJetFromFTraceSq E B) =
      principalChi E B ∧
    Real.sqrt (principalRicciFromFTraceSq E B) =
      principalChi E B := by
  constructor
  · exact principalJetFromF_chi_from_trace E B
  · rw [principalRicciFromF_trace_sq,
      Real.sqrt_sq_eq_abs,
      abs_of_nonneg (principalChi_nonneg E B)]

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


/-- Chronometric unit timelike vector `û_*`, declared here because the canonical
principal null dyad reconstructs it before the later local-clock section. -/
def principalUhat : Fin 4 → ℝ := principalBasis 0

/-- Every principal-frame vector is uniquely reconstructed from its four coordinate
coefficients and the standard principal basis. -/
theorem principalBasis_decomposition
    (v : Fin 4 → ℝ) :
    v = ∑ j : Fin 4, v j • principalBasis j := by
  funext i
  fin_cases i <;> simp [principalBasis]

/-- Linear endomorphisms of the principal frame are determined by their values on
the four principal basis vectors. -/
theorem principalLinearMap_ext_on_basis
    (A B : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
    (h : ∀ j : Fin 4, A (principalBasis j) = B (principalBasis j)) :
    A = B := by
  ext v i
  rw [principalBasis_decomposition v]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j]



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

/-- Minkowski bilinear form in the principal orthonormal frame. -/
def principalMinkowskiBilinear
    (v w : Fin 4 → ℝ) : ℝ :=
  -v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3

/-- Minkowski quadratic form in the principal orthonormal frame. -/
def principalMinkowskiSq (v : Fin 4 → ℝ) : ℝ :=
  -(v 0)^2 + (v 1)^2 + (v 2)^2 + (v 3)^2

theorem principalMinkowskiSq_eq_bilinear
    (v : Fin 4 → ℝ) :
    principalMinkowskiSq v =
      principalMinkowskiBilinear v v := by
  unfold principalMinkowskiSq principalMinkowskiBilinear
  ring

theorem principalMinkowskiBilinear_smul
    (a b : ℝ) (v w : Fin 4 → ℝ) :
    principalMinkowskiBilinear (a • v) (b • w) =
      (a * b) * principalMinkowskiBilinear v w := by
  simp [principalMinkowskiBilinear]
  ring

/-- Canonical inverse square-root normalization for the principal null dyad. -/
def principalInvSqrtTwo : ℝ :=
  (Real.sqrt 2)⁻¹

theorem principalInvSqrtTwo_sq :
    principalInvSqrtTwo^2 = (1 / 2 : ℝ) := by
  have hs0 : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2 : (Real.sqrt 2)^2 = 2 := by norm_num
  unfold principalInvSqrtTwo
  field_simp [hs0]
  nlinarith

/-- Canonically normalized future principal null directions of the Lorentzian Rainich plane. -/
def principalNullK : Fin 4 → ℝ :=
  principalInvSqrtTwo •
    (principalBasis 0 + principalBasis 1)

def principalNullL : Fin 4 → ℝ :=
  principalInvSqrtTwo •
    (principalBasis 0 - principalBasis 1)

/-- The canonical principal null pair is null and cross-normalized by `g(k,l)=-1`. -/
theorem principalNullPair_normalized :
    principalMinkowskiBilinear principalNullK principalNullK = 0 ∧
    principalMinkowskiBilinear principalNullL principalNullL = 0 ∧
    principalMinkowskiBilinear principalNullK principalNullL = -1 := by
  have hc := principalInvSqrtTwo_sq
  constructor
  · simp [principalNullK, principalMinkowskiBilinear,
      principalBasis]
    ring
  · constructor
    · simp [principalNullL, principalMinkowskiBilinear,
        principalBasis]
      ring
    · simp [principalNullK, principalNullL,
        principalMinkowskiBilinear, principalBasis]
      nlinarith

/-- The normalized timelike principal unit is recovered from the null midpoint. -/
theorem principalUhat_from_null_pair :
    principalInvSqrtTwo •
      (principalNullK + principalNullL) =
      principalUhat := by
  have hc := principalInvSqrtTwo_sq
  funext i
  fin_cases i <;>
    simp [principalNullK, principalNullL, principalUhat,
      principalBasis, smul_add, smul_sub, smul_smul] <;>
    nlinarith

/-- The normalized spacelike principal unit is recovered from the null half-difference. -/
theorem principalEhat_from_null_pair :
    principalInvSqrtTwo •
      (principalNullK - principalNullL) =
      principalBasis 1 := by
  have hc := principalInvSqrtTwo_sq
  funext i
  fin_cases i <;>
    simp [principalNullK, principalNullL,
      principalBasis, smul_add, smul_sub, smul_smul] <;>
    nlinarith

/-- Residual principal null boost. -/
def principalBoostedNullK (σ : ℝ) : Fin 4 → ℝ :=
  Real.exp (-σ) • principalNullK

def principalBoostedNullL (σ : ℝ) : Fin 4 → ℝ :=
  Real.exp σ • principalNullL

/-- Every residual boost preserves nullness and the normalization `g(k,l)=-1`. -/
theorem principalBoostedNullPair_normalized (σ : ℝ) :
    principalMinkowskiBilinear
        (principalBoostedNullK σ)
        (principalBoostedNullK σ) = 0 ∧
    principalMinkowskiBilinear
        (principalBoostedNullL σ)
        (principalBoostedNullL σ) = 0 ∧
    principalMinkowskiBilinear
        (principalBoostedNullK σ)
        (principalBoostedNullL σ) = -1 := by
  rcases principalNullPair_normalized with ⟨hk, hl, hkl⟩
  constructor
  · rw [principalBoostedNullK,
      principalMinkowskiBilinear_smul, hk]
    ring
  · constructor
    · rw [principalBoostedNullL,
        principalMinkowskiBilinear_smul, hl]
      ring
    · rw [principalBoostedNullK, principalBoostedNullL,
        principalMinkowskiBilinear_smul, hkl]
      rw [← Real.exp_add]
      simp
      ring

/-- Conversely, every positive rescaling of the normalized null pair that preserves
`g(k,l)=-1` is exactly one residual boost. -/
theorem normalized_null_rescaling_is_boost
    (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hab : a * b = 1) :
    ∃! σ : ℝ,
      a = Real.exp (-σ) ∧ b = Real.exp σ := by
  refine ⟨Real.log b, ?_, ?_⟩
  · constructor
    · rw [Real.exp_neg, Real.exp_log hb]
      exact eq_inv_iff_mul_eq_one.mpr hab
    · exact (Real.exp_log hb).symm
  · intro σ hσ
    apply Real.exp_injective
    exact hσ.2.symm.trans (Real.exp_log hb).symm

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

/-- Physical-metric unit vector `u_* = ω û_*` when `χ=ω²`. -/
def principalPhysicalU (ω : ℝ) : Fin 4 → ℝ :=
  ω • principalUhat


/-- The forced local chronometric covector advances at rate `ω` along physical proper time. -/
@[simp] theorem principalTO_physicalU (ω : ℝ) :
    principalTO (principalPhysicalU ω) = ω := by
  simp [principalTO, principalPhysicalU, principalUhat,
    principalBasis]

/-- If `χ=ω²`, the vector `u_*=ω û_*` is unit timelike for the background metric
`g=χ⁻¹ ĝ`. -/
theorem principalPhysicalU_background_unit
    (χ ω : ℝ)
    (hχ : χ ≠ 0)
    (hχrate : χ = ω^2) :
    χ⁻¹ * principalMinkowskiSq (principalPhysicalU ω) = -1 := by
  have hnorm :
      principalMinkowskiSq (principalPhysicalU ω) = -ω^2 := by
    simp [principalPhysicalU, principalMinkowskiSq,
      principalUhat, principalBasis]
    ring
  have hω2 : ω^2 ≠ 0 := by
    rw [← hχrate]
    exact hχ
  rw [hnorm, hχrate]
  field_simp [hω2]

/-- Thus along the selected physical unit trajectory the local clock differential is
literally `dΘ = ω dτ`; on the normalized chronometric trajectory it is `dΘ=dτ̂`. -/
theorem principal_clock_proper_time_bridge
    (χ ω : ℝ)
    (hχ : χ ≠ 0)
    (hχrate : χ = ω^2) :
    principalTO (principalPhysicalU ω) = ω ∧
    principalTO principalUhat = 1 ∧
    χ⁻¹ * principalMinkowskiSq (principalPhysicalU ω) = -1 := by
  exact ⟨principalTO_physicalU ω,
    principalTO_unit,
    principalPhysicalU_background_unit χ ω hχ hχrate⟩

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


/-! ### Literal pointwise local Iyer-Wald response line -/

section PrincipalPointResponse

variable {HForm : Type*} [AddCommGroup HForm] [Module ℝ HForm]

/-- Restricted pointwise current on the principal rest hyperplane, with a distinguished
oriented spatial volume element `ε_H`. -/
def principalPointResponse
    (ω : ℝ) (εH : HForm) (v : Fin 4 → ℝ) : HForm :=
  (ω / (8 * Real.pi) * principalTO v) • εH

/-- This is exactly the manuscript's local response formula. -/
theorem principalPointResponse_formula
    (ω : ℝ) (εH : HForm) (v : Fin 4 → ℝ) :
    principalPointResponse ω εH v =
      (ω / (8 * Real.pi) * principalTO v) • εH := rfl

/-- On the normalized principal timelike vector the response loses the clock coefficient. -/
@[simp] theorem principalPointResponse_unit
    (ω : ℝ) (εH : HForm) :
    principalPointResponse ω εH principalUhat =
      (ω / (8 * Real.pi)) • εH := by
  simp [principalPointResponse, principalTO_unit]

/-- Every pointwise response is the chronometric scalar times the unit response. -/
theorem principalPointResponse_factor
    (ω : ℝ) (εH : HForm) (v : Fin 4 → ℝ) :
    principalPointResponse ω εH v =
      principalTO v •
        principalPointResponse ω εH principalUhat := by
  rw [principalPointResponse_unit]
  simp [principalPointResponse, smul_smul]
  ring

/-- Positive/nonzero rate and nonzero spatial volume make the normalized pointwise
response genuinely nonzero. -/
theorem principalPointResponse_unit_ne_zero
    (ω : ℝ) (εH : HForm)
    (hω : ω ≠ 0) (hε : εH ≠ 0) :
    principalPointResponse ω εH principalUhat ≠ 0 := by
  rw [principalPointResponse_unit]
  apply smul_ne_zero
  · exact div_ne_zero hω
      (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))
  · exact hε

/-- Therefore the unique response ratio is literally the local chronometric covector. -/
theorem principalPointResponse_ratio_forced
    (ω λ : ℝ) (εH : HForm) (v : Fin 4 → ℝ)
    (hω : ω ≠ 0) (hε : εH ≠ 0)
    (hresponse :
      principalPointResponse ω εH v =
        λ • principalPointResponse ω εH principalUhat) :
    λ = principalTO v := by
  rw [principalPointResponse_factor] at hresponse
  have hunit :=
    principalPointResponse_unit_ne_zero ω εH hω hε
  exact (smul_left_injective ℝ hunit) hresponse.symm

end PrincipalPointResponse

/-! ### Restricted Iyer-Wald coefficient derived directly from the carrier jet -/

/-- Relative coefficient of `ε_H=i_{u_*}ε` against the unit spatial volume in the
adapted principal frame. -/
def principalEpsilonHSpatialCoeff (ω : ℝ) : ℝ :=
  (principalPhysicalU ω) 0

@[simp] theorem principalEpsilonHSpatialCoeff_eq (ω : ℝ) :
    principalEpsilonHSpatialCoeff ω = ω := by
  simp [principalEpsilonHSpatialCoeff, principalPhysicalU,
    principalUhat, principalBasis]

/-- Coefficient of `w_Y(v)|_H=(8π)⁻¹ i_{J(v)}ε|_H` against the unit spatial volume. -/
def principalBridgeSpatialCoeff
    (ω : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  (1 / (8 * Real.pi)) * principalJetFromRate ω v 0

/-- The fixed-point jet itself forces the local Iyer-Wald formula relative to `ε_H`. -/
theorem principalBridgeSpatialCoeff_formula
    (ω : ℝ) (v : Fin 4 → ℝ) :
    principalBridgeSpatialCoeff ω v =
      (ω / (8 * Real.pi) * principalTO v) *
        principalEpsilonHSpatialCoeff ω := by
  unfold principalBridgeSpatialCoeff principalJetFromRate
  rw [principalEpsilonHSpatialCoeff_eq]
  simp [principalJetInvolution, principalTO]
  ring

/-- On the normalized timelike unit the restricted bridge coefficient is exactly the
normalization response used in the manuscript. -/
theorem principalBridgeSpatialCoeff_unit
    (ω : ℝ) :
    principalBridgeSpatialCoeff ω principalUhat =
      (ω / (8 * Real.pi)) *
        principalEpsilonHSpatialCoeff ω := by
  rw [principalBridgeSpatialCoeff_formula, principalTO_unit]
  ring

/-- Every restricted carrier current is the clock value times the normalized unit current. -/
theorem principalBridgeSpatialCoeff_factor
    (ω : ℝ) (v : Fin 4 → ℝ) :
    principalBridgeSpatialCoeff ω v =
      principalTO v *
        principalBridgeSpatialCoeff ω principalUhat := by
  rw [principalBridgeSpatialCoeff_formula,
    principalBridgeSpatialCoeff_unit]
  ring

/-- For nonzero clock rate, the normalized carrier-current coefficient is nonzero. -/
theorem principalBridgeSpatialCoeff_unit_ne_zero
    (ω : ℝ) (hω : ω ≠ 0) :
    principalBridgeSpatialCoeff ω principalUhat ≠ 0 := by
  rw [principalBridgeSpatialCoeff_unit,
    principalEpsilonHSpatialCoeff_eq]
  exact mul_ne_zero
    (div_ne_zero hω
      (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)))
    hω

/-- Therefore the pointwise coefficient ratio derived from the actual jet is uniquely
the chronometric covector `T_O`. -/
theorem principalBridgeSpatialCoeff_ratio_forced
    (ω λ : ℝ) (v : Fin 4 → ℝ)
    (hω : ω ≠ 0)
    (hresponse :
      principalBridgeSpatialCoeff ω v =
        λ * principalBridgeSpatialCoeff ω principalUhat) :
    λ = principalTO v := by
  rw [principalBridgeSpatialCoeff_factor] at hresponse
  exact (mul_right_cancel₀
    (principalBridgeSpatialCoeff_unit_ne_zero ω hω))
    hresponse.symm


/-! ### Principal-frame realization of the local stress-visible quotient -/

/-- Spatial hyperplane selected by the normalized principal observer. -/
def principalSpatialSubmodule : Submodule ℝ (Fin 4 → ℝ) where
  carrier := {v | v 0 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp [hx, hy]
  smul_mem' := by
    intro c x hx
    simp [hx]

/-- The local clock kernel is exactly the principal spatial hyperplane. -/
theorem principalTO_ker_eq_spatial :
    LinearMap.ker
      ({ toFun := principalTO
         map_add' := by intro x y; rfl
         map_smul' := by intro c x; rfl } :
        (Fin 4 → ℝ) →ₗ[ℝ] ℝ) =
      principalSpatialSubmodule := by
  ext v
  simp [principalTO, principalSpatialSubmodule]

/-- Principal local clock covector as a linear map. -/
def principalTOLinear :
    (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun := principalTO
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl

@[simp] theorem principalTOLinear_apply (v : Fin 4 → ℝ) :
    principalTOLinear v = principalTO v := rfl


/-- The local clock linear map evaluates to `ω` on the physical unit tangent. -/
@[simp] theorem principalTOLinear_physicalU (ω : ℝ) :
    principalTOLinear (principalPhysicalU ω) = ω := by
  simpa [principalTOLinear_apply] using principalTO_physicalU ω

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

/-- Carrier endomorphism normalized by its positive Rainich magnitude. -/
def normalizedCarrierEndomorphism
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] V) (χ : ℝ) :
    V →ₗ[ℝ] V :=
  (χ⁻¹) • J

/-- If the mixed carrier and its invariant magnitude acquire the same nonzero
homothety weight, the normalized involution is unchanged. -/
theorem normalizedCarrierEndomorphism_scale_invariant
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] V) (χ c : ℝ)
    (hχ : χ ≠ 0) (hc : c ≠ 0) :
    normalizedCarrierEndomorphism (c • J) (c * χ) =
      normalizedCarrierEndomorphism J χ := by
  ext v
  simp [normalizedCarrierEndomorphism, smul_smul]
  field_simp [hχ, hc]

/-- In particular the common Einstein-Maxwell weight `ρ⁻²` cancels identically
between the mixed carrier and `χ`. -/
theorem normalizedCarrierEndomorphism_common_scale
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] V) (χ ρ : ℝ)
    (hχ : χ ≠ 0) (hρ : ρ ≠ 0) :
    normalizedCarrierEndomorphism
        (((ρ⁻¹)^2) • J) (((ρ⁻¹)^2) * χ) =
      normalizedCarrierEndomorphism J χ := by
  exact normalizedCarrierEndomorphism_scale_invariant
    J χ ((ρ⁻¹)^2) hχ (pow_ne_zero 2 (inv_ne_zero hρ))

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

/-- The principal projectors are representative-independent whenever the normalized
carrier is representative-independent. -/
theorem involution_projectors_scale_invariant
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] V) (χ c : ℝ)
    (hχ : χ ≠ 0) (hc : c ≠ 0) (v : V) :
    involutionProjPlus
        (normalizedCarrierEndomorphism (c • J) (c * χ)) v =
      involutionProjPlus
        (normalizedCarrierEndomorphism J χ) v ∧
    involutionProjMinus
        (normalizedCarrierEndomorphism (c • J) (c * χ)) v =
      involutionProjMinus
        (normalizedCarrierEndomorphism J χ) v := by
  rw [normalizedCarrierEndomorphism_scale_invariant J χ c hχ hc]

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


/-- Common Einstein-Maxwell representative invariance itself forces the required
one-homogeneity.  Here `r2` is the positive metric homothety factor:
`g ↦ r2 g`, `χ ↦ χ/r2`, and invariance of `f(χ)g` means
`f(χ/r2) r2 = f(χ)`. -/
theorem common_scale_invariance_implies_homogeneous
    (f : ℝ → ℝ)
    (hinv :
      ∀ r2 χ : ℝ,
        0 < r2 → 0 < χ →
        f (χ / r2) * r2 = f χ) :
    ∀ c χ : ℝ,
      0 < c → 0 < χ →
      f (c * χ) = c * f χ := by
  intro c χ hc hχ
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hr2 : 0 < (1 / c : ℝ) := by positivity
  have h := hinv (1 / c) χ hr2 hχ
  have harg : χ / (1 / c) = c * χ := by
    field_simp [hc0]
    ring
  rw [harg] at h
  calc
    f (c * χ)
        = c * (f (c * χ) * (1 / c)) := by
            field_simp [hc0]
    _ = c * f χ := by rw [h]

/-- Therefore common-scale invariance already forces the linear form
`f(χ)=f(1)χ`. -/
theorem common_scale_invariance_forces_linear_factor
    (f : ℝ → ℝ)
    (hinv :
      ∀ r2 χ : ℝ,
        0 < r2 → 0 < χ →
        f (χ / r2) * r2 = f χ)
    (χ : ℝ) (hχ : 0 < χ) :
    f χ = f 1 * χ := by
  exact homogeneous_conformal_factor f
    (common_scale_invariance_implies_homogeneous f hinv)
    χ hχ

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

/-! ### Carrier scaling from tensor index weights -/

/-- Squared carrier contraction under a constant common metric homothety.
Two raised indices contribute the factor `ρ⁻⁴`. -/
def carrierContractionUnderScale (ρ Jsq : ℝ) : ℝ :=
  (ρ⁻¹)^4 * Jsq

/-- The positive Rainich magnitude built from the squared contraction. -/
def carrierMagnitudeFromContraction (Jsq : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.sqrt Jsq

/-- Positive square-root homogeneity converts the forced contraction scaling
`ρ⁻⁴` into the carrier scaling `ρ⁻²`. -/
theorem carrierMagnitude_common_scale
    (ρ Jsq : ℝ)
    (hρ : 0 < ρ)
    (hJ : 0 ≤ Jsq) :
    carrierMagnitudeFromContraction
      (carrierContractionUnderScale ρ Jsq) =
      (ρ⁻¹)^2 * carrierMagnitudeFromContraction Jsq := by
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hcpos : 0 < (ρ⁻¹)^2 := by positivity
  have hc : 0 ≤ (ρ⁻¹)^2 := le_of_lt hcpos
  have hscale :
      (ρ⁻¹)^4 = ((ρ⁻¹)^2)^2 := by
    field_simp [hρ0]
    ring
  have hscaled :
      0 ≤ carrierContractionUnderScale ρ Jsq := by
    unfold carrierContractionUnderScale
    positivity
  have hleftsq :
      (Real.sqrt
        (carrierContractionUnderScale ρ Jsq))^2 =
        carrierContractionUnderScale ρ Jsq :=
    Real.sq_sqrt hscaled
  have hrightsq :
      (((ρ⁻¹)^2) * Real.sqrt Jsq)^2 =
        carrierContractionUnderScale ρ Jsq := by
    rw [mul_pow, Real.sq_sqrt hJ]
    unfold carrierContractionUnderScale
    rw [hscale]
    ring
  have hleftnonneg :
      0 ≤ Real.sqrt
        (carrierContractionUnderScale ρ Jsq) :=
    Real.sqrt_nonneg _
  have hrightnonneg :
      0 ≤ ((ρ⁻¹)^2) * Real.sqrt Jsq :=
    mul_nonneg hc (Real.sqrt_nonneg _)
  have hsqrt :
      Real.sqrt (carrierContractionUnderScale ρ Jsq) =
        ((ρ⁻¹)^2) * Real.sqrt Jsq := by
    nlinarith
  unfold carrierMagnitudeFromContraction
  rw [hsqrt]
  ring

/-- Thus the manuscript's common-scale law `χ ↦ ρ⁻²χ` is a consequence of the
two inverse-metric weights in the invariant contraction, not an independent postulate. -/
theorem carrier_chi_common_scale
    (ρ Jsq χ : ℝ)
    (hρ : 0 < ρ)
    (hJ : 0 ≤ Jsq)
    (hχ : χ = carrierMagnitudeFromContraction Jsq) :
    carrierMagnitudeFromContraction
      (carrierContractionUnderScale ρ Jsq) =
      (ρ⁻¹)^2 * χ := by
  rw [hχ]
  exact carrierMagnitude_common_scale ρ Jsq hρ hJ

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


/-- Strong form of the manuscript's conformal-normalization argument: representative
invariance plus unit-involution normalization force `f(χ)=χ` directly, with
one-homogeneity no longer supplied as a premise. -/
theorem conformal_factor_forced_from_common_scale
    (f : ℝ → ℝ)
    (hinv :
      ∀ r2 χ : ℝ,
        0 < r2 → 0 < χ →
        f (χ / r2) * r2 = f χ)
    (χ : ℝ) (hχ : 0 < χ)
    (hC : 0 < f 1)
    (hunit : χ^2 / (f χ)^2 = 1) :
    f χ = χ := by
  exact conformal_factor_forced f
    (common_scale_invariance_implies_homogeneous f hinv)
    χ hχ hC hunit


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


/-- The explicit reciprocal action, curvature carrier, and operational optical velocity
are the same projective rapidity observable. -/
theorem action_carrier_optical_ratio_identity
    (S η s : ℝ) (hS : S ≠ 0) (hη : η ≠ 0) :
    - relativeActionDefect S s /
        relativeActionValue S S s =
      - carrierOdd η s / carrierEven η s ∧
    - relativeActionDefect S s /
        relativeActionValue S S s =
      opticalEval RO (opticalObserver s) /
        opticalEval TO (opticalObserver s) := by
  rw [relativeAction_defect_ratio S s hS,
    carrier_ratio η s hη,
    optical_velocity_ratio s]

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

/-! ### Reciprocal-character derivation of the odd presymplectic sector -/

section RelativeSymplecticSector

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Evaluation of the common/even presymplectic sector under the relative characters
`e^{-s}` and `e^s`. -/
def relativeSymplecticPlusEval
    (ΩG ΩM : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (s : ℝ) (x y : V) : ℝ :=
  Real.exp (-s) * ΩG x y +
    Real.exp s * ΩM x y

/-- Linearity in the Lagrangian forces the same reciprocal character on the
presymplectic current. -/
theorem relativeSymplecticPlusEval_from_lagrangian
    {L : Type*} [AddCommGroup L] [Module ℝ L]
    (omegaOfL : L →ₗ[ℝ] (V →ₗ[ℝ] V →ₗ[ℝ] ℝ))
    (LG LM : L) (s : ℝ) (x y : V) :
    relativeSymplecticPlusEval
        (omegaOfL LG) (omegaOfL LM) s x y =
      omegaOfL (reciprocalLagrangian LG LM s) x y := by
  rw [linearDescendant_reciprocal omegaOfL LG LM s]
  simp [relativeSymplecticPlusEval]

/-- The odd fixed-point presymplectic descendant is the image of the Lagrangian
normal jet, up to the universal factor one half. -/
theorem relativeSymplecticMinus_from_lagrangian_normalJet
    {L : Type*} [AddCommGroup L] [Module ℝ L]
    (omegaOfL : L →ₗ[ℝ] (V →ₗ[ℝ] V →ₗ[ℝ] ℝ))
    (LG LM : L) (x y : V) :
    relativeSymplecticMinusEval
        (omegaOfL LG) (omegaOfL LM) x y =
      (1 / 2 : ℝ) *
        omegaOfL (reciprocalLagrangianNormalJet LG LM) x y := by
  rw [linearDescendant_normalJet omegaOfL LG LM]
  simp [relativeSymplecticMinusEval]
  ring

/-- Exchange-odd half-difference selected at the fixed point. -/
def relativeSymplecticMinusEval
    (ΩG ΩM : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (x y : V) : ℝ :=
  (-ΩG x y + ΩM x y) / 2

/-- The normal derivative of the even sector sum is exactly twice the odd sector. -/
theorem relativeSymplecticPlus_hasDerivAt_zero
    (ΩG ΩM : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (x y : V) :
    HasDerivAt
      (fun s : ℝ =>
        relativeSymplecticPlusEval ΩG ΩM s x y)
      (2 * relativeSymplecticMinusEval ΩG ΩM x y) 0 := by
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) 0 :=
    (hasDerivAt_id 0).neg
  have hGexp :
      HasDerivAt (fun s : ℝ => Real.exp (-s)) (-1) 0 := by
    simpa using (Real.hasDerivAt_exp 0).comp 0 hneg
  have hG :=
    hGexp.mul_const (ΩG x y)
  have hM :=
    (Real.hasDerivAt_exp 0).mul_const (ΩM x y)
  unfold relativeSymplecticPlusEval
  convert hG.add hM using 1
  · funext s
    rfl
  · unfold relativeSymplecticMinusEval
    norm_num
    ring

/-- Therefore the manuscript definition
`Ω_-=(1/2)L_Y Ω_+` is an identity of the reciprocal sector characters. -/
theorem relativeSymplecticMinus_eq_half_derivative
    (ΩG ΩM : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (x y : V) :
    (1 / 2 : ℝ) *
      deriv
        (fun s : ℝ =>
          relativeSymplecticPlusEval ΩG ΩM s x y) 0 =
      relativeSymplecticMinusEval ΩG ΩM x y := by
  rw [(relativeSymplecticPlus_hasDerivAt_zero
    ΩG ΩM x y).deriv]
  ring

/-- Exchange of the two sectors reverses the odd presymplectic descendant. -/
theorem relativeSymplecticMinus_exchange
    (ΩG ΩM : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (x y : V) :
    relativeSymplecticMinusEval ΩM ΩG x y =
      - relativeSymplecticMinusEval ΩG ΩM x y := by
  unfold relativeSymplecticMinusEval
  ring

/-- The exchange-odd descendant as an actual bilinear linear map. -/
def relativeSymplecticMinus
    (ΩG ΩM : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  (-1 / 2 : ℝ) • ΩG + (1 / 2 : ℝ) • ΩM

@[simp] theorem relativeSymplecticMinus_apply
    (ΩG ΩM : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (x y : V) :
    relativeSymplecticMinus ΩG ΩM x y =
      relativeSymplecticMinusEval ΩG ΩM x y := by
  simp [relativeSymplecticMinus,
    relativeSymplecticMinusEval]
  ring

/-- The half-normal derivative identity therefore holds as equality with the actual
odd bilinear form at every pair of tangent vectors. -/
theorem relativeSymplecticMinus_apply_eq_half_derivative
    (ΩG ΩM : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (x y : V) :
    relativeSymplecticMinus ΩG ΩM x y =
      (1 / 2 : ℝ) *
        deriv
          (fun s : ℝ =>
            relativeSymplecticPlusEval ΩG ΩM s x y) 0 := by
  rw [relativeSymplecticMinus_apply,
    relativeSymplecticMinus_eq_half_derivative]

/-- Contraction with the already-fixed common-scale Euler direction gives the
relative homogeneous Liouville covector. -/
def relativeLiouvilleCovector
    (ΩG ΩM : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (D : V) : V →ₗ[ℝ] ℝ :=
  relativeSymplecticMinus ΩG ΩM D

@[simp] theorem relativeLiouvilleCovector_apply
    (ΩG ΩM : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (D X : V) :
    relativeLiouvilleCovector ΩG ΩM D X =
      relativeSymplecticMinusEval ΩG ΩM D X := by
  simp [relativeLiouvilleCovector]

/-- If the sector two-forms are skew, the odd descendant is skew as well. -/
theorem relativeSymplecticMinus_skew
    (ΩG ΩM : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hG : ∀ x y : V, ΩG x y = - ΩG y x)
    (hM : ∀ x y : V, ΩM x y = - ΩM y x)
    (x y : V) :
    relativeSymplecticMinus ΩG ΩM x y =
      - relativeSymplecticMinus ΩG ΩM y x := by
  simp [relativeSymplecticMinus_apply,
    relativeSymplecticMinusEval,
    hG x y, hM x y, hG y x, hM y x]
  ring

/-- Consequently the homogeneous primitive is horizontal on the Euler direction:
`ι_D Ω_-(D)=0`. -/
theorem relativeLiouvilleCovector_horizontal
    (ΩG ΩM : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (D : V)
    (hG : ∀ x y : V, ΩG x y = - ΩG y x)
    (hM : ∀ x y : V, ΩM x y = - ΩM y x) :
    relativeLiouvilleCovector ΩG ΩM D D = 0 := by
  have hsk :=
    relativeSymplecticMinus_skew
      ΩG ΩM hG hM D D
  have hEq :
      relativeLiouvilleCovector ΩG ΩM D D =
        relativeSymplecticMinus ΩG ΩM D D := rfl
  rw [hEq]
  linarith

end RelativeSymplecticSector

/-! ### Carrier-current bridge forced by the Einstein-Maxwell jet -/

section CarrierCurrentBridge

variable {V W : Type*}
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Pointwise compensated current constructed from the fixed-point carrier:
`w_Y=(8π)⁻¹ i_{J(v)} ε`.  The map `iε` abstracts contraction with the oriented volume form. -/
def carrierJetCurrent
    (J : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W) :
    V →ₗ[ℝ] W :=
  (1 / (8 * Real.pi)) • (iε.comp J)

/-- Stress-current form appearing on the other side of the bridge. -/
def stressBridgeCurrent
    (T : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W) :
    V →ₗ[ℝ] W :=
  (-2 : ℝ) • (iε.comp T)

/-- The field-equation jet `J=-16πT` forces the two pointwise current formulas to be
identical.  No independent normalization or sign remains. -/
theorem carrierJetCurrent_eq_stressBridgeCurrent
    (J T : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W)
    (hJ : J = (-16 * Real.pi) • T) :
    carrierJetCurrent J iε =
      stressBridgeCurrent T iε := by
  ext v
  rw [hJ]
  simp [carrierJetCurrent, stressBridgeCurrent]
  field_simp [ne_of_gt Real.pi_pos]
  ring

/-- Abstract hypersurface integral of the unscaled stress current. -/
def stressResponse
    (integrate : W →ₗ[ℝ] ℝ)
    (T : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W) :
    V →ₗ[ℝ] ℝ :=
  integrate.comp (iε.comp T)

/-- Integrated compensated carrier current. -/
def carrierBulkResponse
    (integrate : W →ₗ[ℝ] ℝ)
    (J : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W) :
    V →ₗ[ℝ] ℝ :=
  integrate.comp (carrierJetCurrent J iε)

/-- Hypersurface integration preserves the forced bridge:
`∫W_Y=-2 ell`. -/
theorem carrierBulkResponse_eq_minus_two_stressResponse
    (integrate : W →ₗ[ℝ] ℝ)
    (J T : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W)
    (hJ : J = (-16 * Real.pi) • T) :
    carrierBulkResponse integrate J iε =
      (-2 : ℝ) • stressResponse integrate T iε := by
  ext v
  unfold carrierBulkResponse stressResponse
  rw [carrierJetCurrent_eq_stressBridgeCurrent J T iε hJ]
  simp [stressBridgeCurrent]

/-- Scalar evaluation version of the pointwise bridge, useful for direct comparison with
the manuscript's component formula. -/
theorem carrier_bridge_scalar
    (J T volumeCoeff ξCoeff : ℝ)
    (hJ : J = -16 * Real.pi * T) :
    (1 / (8 * Real.pi)) * volumeCoeff * J * ξCoeff =
      -2 * volumeCoeff * T * ξCoeff := by
  rw [hJ]
  field_simp [ne_of_gt Real.pi_pos]
  ring

/-- The characteristic covector prescribed by the manuscript is the negative half of
the integrated carrier current. -/
def halfCarrierBulkCurrent
    (integrate : W →ₗ[ℝ] ℝ)
    (J : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W) :
    V →ₗ[ℝ] ℝ :=
  (-1 / 2 : ℝ) • carrierBulkResponse integrate J iε

/-- The field-equation jet forces this negative-half bulk current to be exactly the
integrated Maxwell stress response.  Hence the factor `-1/2` in `Lambda` is fixed,
not a normalization convention. -/
theorem halfCarrierBulkCurrent_eq_stressResponse
    (integrate : W →ₗ[ℝ] ℝ)
    (J T : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W)
    (hJ : J = (-16 * Real.pi) • T) :
    halfCarrierBulkCurrent integrate J iε =
      stressResponse integrate T iε := by
  rw [halfCarrierBulkCurrent,
    carrierBulkResponse_eq_minus_two_stressResponse
      integrate J T iε hJ]
  ext v
  simp
  ring

/-- Pointwise counterpart: negative one half of the carrier-current coefficient is the
unscaled stress contraction. -/
theorem half_carrier_bridge_scalar
    (J T volumeCoeff ξCoeff : ℝ)
    (hJ : J = -16 * Real.pi * T) :
    (-1 / 2 : ℝ) *
      ((1 / (8 * Real.pi)) * volumeCoeff * J * ξCoeff) =
      volumeCoeff * T * ξCoeff := by
  rw [carrier_bridge_scalar J T volumeCoeff ξCoeff hJ]
  ring

end CarrierCurrentBridge

/-! ### Boundary-compensated Iyer-Wald sign algebra -/

/-- Common-character-removed relative constraint residual when the gravity and Maxwell
constraint contributions agree at the fixed point. -/
def relativeConstraintResidual (ell s : ℝ) : ℝ :=
  Real.exp (-s) * (ell - Real.exp (2 * s) * ell)

/-- The constraint residual is the same reciprocal Lagrangian descendant with
opposite sector values. -/
theorem relativeConstraintResidual_eq_reciprocalLagrangian
    (ell s : ℝ) :
    relativeConstraintResidual ell s =
      reciprocalLagrangian ell (-ell) s := by
  unfold relativeConstraintResidual reciprocalLagrangian
  simp [smul_eq_mul]
  rw [show Real.exp (-s) * Real.exp (2 * s) = Real.exp s by
    rw [← Real.exp_add]
    congr 1
    ring]
  ring

/-- The `-2 ell` constraint variation is therefore the literal normal jet of the
same reciprocal Lagrangian character. -/
theorem relativeConstraintResidual_deriv_from_lagrangian
    (ell : ℝ) :
    deriv (relativeConstraintResidual ell) 0 = -2 * ell := by
  have hD : ℝ →ₗ[ℝ] ℝ := LinearMap.id
  have h := linearDescendant_reciprocal_hasDerivAt_zero hD ell (-ell)
  have heq :
      relativeConstraintResidual ell =
        fun s : ℝ => hD (reciprocalLagrangian ell (-ell) s) := by
    funext s
    rw [relativeConstraintResidual_eq_reciprocalLagrangian]
    rfl
  rw [heq, h.deriv]
  simp

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

/-! ### First-variation derivation of the Iyer-Wald operator identity -/

section FirstVariationNoetherDerivation

variable {L C : Type*}
  [AddCommGroup L] [Module ℝ L]
  [AddCommGroup C] [Module ℝ C]

/-- Covariant first-variation data one logical layer closer to the Lagrangian itself.
`deltaL = euler + dTheta` is the actual first-variation decomposition; Cartan is
imposed only on the boundary-potential derivative; and the varied Noether-current
decomposition is stated before any Iyer-Wald current is defined. -/
structure LagrangianVariationNoetherOperators where
  deltaL : L →ₗ[ℝ] C
  euler : L →ₗ[ℝ] C
  dTheta : L →ₗ[ℝ] C
  contractGauge : C →ₗ[ℝ] C
  deltaThetaGauge : L →ₗ[ℝ] C
  lieTheta : L →ₗ[ℝ] C
  dContractTheta : L →ₗ[ℝ] C
  deltaConstraint : L →ₗ[ℝ] C
  dDeltaCharge : L →ₗ[ℝ] C
  first_variation : deltaL = euler + dTheta
  cartan_on_dTheta :
    contractGauge.comp dTheta = lieTheta - dContractTheta
  noether_decomposition_variation :
    deltaThetaGauge - contractGauge.comp deltaL =
      deltaConstraint + dDeltaCharge

/-- Ordered presymplectic current derived from the potential variation. -/
def LagrangianVariationNoetherOperators.omegaYX
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C)) :
    L →ₗ[ℝ] C :=
  D.deltaThetaGauge - D.lieTheta

/-- Boundary variation `delta Q_xi - i_xi theta`. -/
def LagrangianVariationNoetherOperators.dB
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C)) :
    L →ₗ[ℝ] C :=
  D.dDeltaCharge - D.dContractTheta

/-- Off-shell constraint descendant with the manuscript sign convention. -/
def LagrangianVariationNoetherOperators.constraint
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C)) :
    L →ₗ[ℝ] C :=
  -(D.deltaConstraint + D.contractGauge.comp D.euler)

/-- Reversed presymplectic ordering is fixed by antisymmetry. -/
def LagrangianVariationNoetherOperators.omegaXY
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C)) :
    L →ₗ[ℝ] C :=
  -D.omegaYX

/-- Contracting the actual first-variation equation and using Cartan forces the
contracted variation formula used in the Noether calculation. -/
theorem LagrangianVariationNoetherOperators.contracted_first_variation
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C)) :
    D.contractGauge.comp D.deltaL =
      D.contractGauge.comp D.euler + D.lieTheta - D.dContractTheta := by
  ext X
  have hFV := LinearMap.congr_fun D.first_variation X
  have hC := LinearMap.congr_fun D.cartan_on_dTheta X
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply] at hC ⊢
  calc
    D.contractGauge (D.deltaL X)
        = D.contractGauge (D.euler X + D.dTheta X) := by rw [hFV]
    _ = D.contractGauge (D.euler X) + D.contractGauge (D.dTheta X) := by
      rw [map_add]
    _ = D.contractGauge (D.euler X) +
          (D.lieTheta X - D.dContractTheta X) := by rw [hC]
    _ = D.contractGauge (D.euler X) + D.lieTheta X -
          D.dContractTheta X := by module

/-- Off-shell Iyer-Wald is now a theorem of the Lagrangian first variation, Cartan,
and varied Noether decomposition. It is not stored as a premise. -/
theorem LagrangianVariationNoetherOperators.iyerWald_operator_identity
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C)) :
    D.omegaYX = D.dB - D.constraint := by
  ext X
  have hN := LinearMap.congr_fun D.noether_decomposition_variation X
  have hFV := LinearMap.congr_fun D.contracted_first_variation X
  simp only [LagrangianVariationNoetherOperators.omegaYX,
    LagrangianVariationNoetherOperators.dB,
    LagrangianVariationNoetherOperators.constraint,
    LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.neg_apply] at hN hFV ⊢
  rw [hFV] at hN
  module

theorem LagrangianVariationNoetherOperators.iyerWald_identity_apply
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C))
    (X : L) :
    D.omegaYX X = D.dB X - D.constraint X := by
  exact LinearMap.congr_fun D.iyerWald_operator_identity X

/-- The compensated reversed current equals the constraint descendant and hence has
no independent sign or normalization freedom. -/
theorem LagrangianVariationNoetherOperators.compensated_eq_constraint
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C))
    (X : L) :
    D.omegaXY X + D.dB X = D.constraint X := by
  unfold LagrangianVariationNoetherOperators.omegaXY
  rw [D.iyerWald_identity_apply]
  module

/-- Existence and uniqueness of the compensated current already follows at this
first-variation level. -/
theorem LagrangianVariationNoetherOperators.omegaXY_existsUnique
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C)) :
    ∃! W : L →ₗ[ℝ] C,
      ∀ X : L, W X + D.dB X = D.constraint X := by
  refine ⟨D.omegaXY, D.compensated_eq_constraint, ?_⟩
  intro W hW
  ext X
  have hEq : W X + D.dB X = D.omegaXY X + D.dB X :=
    (hW X).trans (D.compensated_eq_constraint X).symm
  exact add_right_cancel hEq

/-- Reciprocal gravity/Maxwell sector values force the complete relative-normal
constraint response from the Lagrangian first-variation package. -/
theorem LagrangianVariationNoetherOperators.constraint_normalJet_of_opposite
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C))
    (LG LM : L) (ell : C)
    (hG : D.constraint LG = ell)
    (hM : D.constraint LM = -ell) :
    D.constraint (reciprocalLagrangianNormalJet LG LM) =
      (-2 : ℝ) • ell :=
  linearDescendant_normalJet_of_opposite
    D.constraint LG LM ell hG hM

/-- The full boundary-compensated relative-normal current is therefore fixed before
introducing any Iyer-Wald operator package. -/
theorem LagrangianVariationNoetherOperators.compensated_relative_normal
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C))
    (LG LM : L) (ell : C)
    (hG : D.constraint LG = ell)
    (hM : D.constraint LM = -ell) :
    D.omegaXY (reciprocalLagrangianNormalJet LG LM) +
        D.dB (reciprocalLagrangianNormalJet LG LM) =
      (-2 : ℝ) • ell := by
  rw [D.compensated_eq_constraint]
  exact D.constraint_normalJet_of_opposite LG LM ell hG hM

/-- Primitive covariant-phase-space descendants. At this level no Iyer-Wald,
Cartan-first-variation, or Noether-decomposition identity is supplied as a premise;
the composite operators are defined from these primitive descendants. -/
structure PrimitiveNoetherOperators where
  deltaThetaGauge : L →ₗ[ℝ] C
  lieTheta : L →ₗ[ℝ] C
  contractEuler : L →ₗ[ℝ] C
  dContractTheta : L →ₗ[ℝ] C
  dDeltaCharge : L →ₗ[ℝ] C

def PrimitiveNoetherOperators.contractDeltaL
    (D : PrimitiveNoetherOperators (L:=L) (C:=C)) :
    L →ₗ[ℝ] C :=
  D.contractEuler + D.lieTheta - D.dContractTheta

def PrimitiveNoetherOperators.deltaNoether
    (D : PrimitiveNoetherOperators (L:=L) (C:=C)) :
    L →ₗ[ℝ] C :=
  D.deltaThetaGauge - D.contractDeltaL

def PrimitiveNoetherOperators.deltaConstraint
    (D : PrimitiveNoetherOperators (L:=L) (C:=C)) :
    L →ₗ[ℝ] C :=
  D.deltaNoether - D.dDeltaCharge

/-- Primitive linear descendants used before invoking the Iyer-Wald identity.
They encode only: variation of the Noether-current definition, contraction of
the Lagrangian first-variation formula together with Cartan's identity, and
variation of the Noether-current decomposition into constraint plus exact charge. -/
structure FirstVariationNoetherOperators where
  deltaThetaGauge : L →ₗ[ℝ] C
  lieTheta : L →ₗ[ℝ] C
  contractDeltaL : L →ₗ[ℝ] C
  contractEuler : L →ₗ[ℝ] C
  dContractTheta : L →ₗ[ℝ] C
  deltaNoether : L →ₗ[ℝ] C
  deltaConstraint : L →ₗ[ℝ] C
  dDeltaCharge : L →ₗ[ℝ] C
  noether_current_variation :
    deltaNoether = deltaThetaGauge - contractDeltaL
  first_variation_cartan :
    contractDeltaL = contractEuler + lieTheta - dContractTheta
  noether_decomposition_variation :
    deltaNoether = deltaConstraint + dDeltaCharge

/-- Forgetting the explicit `deltaL = E deltaPhi + dTheta` layer recovers the older
first-variation package. -/
def LagrangianVariationNoetherOperators.toFirstVariationNoetherOperators
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C)) :
    FirstVariationNoetherOperators (L:=L) (C:=C) where
  deltaThetaGauge := D.deltaThetaGauge
  lieTheta := D.lieTheta
  contractDeltaL := D.contractGauge.comp D.deltaL
  contractEuler := D.contractGauge.comp D.euler
  dContractTheta := D.dContractTheta
  deltaNoether := D.deltaThetaGauge - D.contractGauge.comp D.deltaL
  deltaConstraint := D.deltaConstraint
  dDeltaCharge := D.dDeltaCharge
  noether_current_variation := by rfl
  first_variation_cartan := D.contracted_first_variation
  noether_decomposition_variation := D.noether_decomposition_variation

/-- The Iyer-Wald current derived after forgetting is exactly the current derived
directly from the Lagrangian first variation. -/
@[simp] theorem LagrangianVariationNoetherOperators.toFirstVariation_omegaYX
    (D : LagrangianVariationNoetherOperators (L:=L) (C:=C)) :
    D.toFirstVariationNoetherOperators.omegaYX = D.omegaYX := by
  rfl

/-- The three first-variation/Noether identities are now consequences of definitions. -/
def PrimitiveNoetherOperators.toFirstVariationNoetherOperators
    (D : PrimitiveNoetherOperators (L:=L) (C:=C)) :
    FirstVariationNoetherOperators (L:=L) (C:=C) where
  deltaThetaGauge := D.deltaThetaGauge
  lieTheta := D.lieTheta
  contractDeltaL := D.contractDeltaL
  contractEuler := D.contractEuler
  dContractTheta := D.dContractTheta
  deltaNoether := D.deltaNoether
  deltaConstraint := D.deltaConstraint
  dDeltaCharge := D.dDeltaCharge
  noether_current_variation := by rfl
  first_variation_cartan := by rfl
  noether_decomposition_variation := by
    unfold PrimitiveNoetherOperators.deltaConstraint
    module

/-- Presymplectic current in the ordered pair (ordinary variation, gauge variation). -/
def FirstVariationNoetherOperators.omegaYX
    (D : FirstVariationNoetherOperators (L:=L) (C:=C)) :
    L →ₗ[ℝ] C :=
  D.deltaThetaGauge - D.lieTheta

/-- Boundary operator δQ_ξ - ι_ξ θ. -/
def FirstVariationNoetherOperators.dB
    (D : FirstVariationNoetherOperators (L:=L) (C:=C)) :
    L →ₗ[ℝ] C :=
  D.dDeltaCharge - D.dContractTheta

/-- Constraint operator in the sign convention used by the manuscript's
`omegaYX = dB - constraint` identity. -/
def FirstVariationNoetherOperators.constraint
    (D : FirstVariationNoetherOperators (L:=L) (C:=C)) :
    L →ₗ[ℝ] C :=
  -(D.deltaConstraint + D.contractEuler)

/-- The off-shell Iyer-Wald operator identity is not an input at this level.
It follows algebraically from the first-variation, Cartan, and Noether-decomposition
identities above. -/
theorem FirstVariationNoetherOperators.iyerWald_operator_identity
    (D : FirstVariationNoetherOperators (L:=L) (C:=C)) :
    D.omegaYX = D.dB - D.constraint := by
  ext X
  have hJ := LinearMap.congr_fun D.noether_current_variation X
  have hFV := LinearMap.congr_fun D.first_variation_cartan X
  have hN := LinearMap.congr_fun D.noether_decomposition_variation X
  simp only [FirstVariationNoetherOperators.omegaYX,
    FirstVariationNoetherOperators.dB,
    FirstVariationNoetherOperators.constraint,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply]
  module

/-- Pointwise form of the derived off-shell identity. -/
theorem FirstVariationNoetherOperators.iyerWald_identity_apply
    (D : FirstVariationNoetherOperators (L:=L) (C:=C))
    (X : L) :
    D.omegaYX X = D.dB X - D.constraint X := by
  exact LinearMap.congr_fun D.iyerWald_operator_identity X

/-- The boundary-compensated reversed current is already fixed by the
first-variation data, before introducing any independent Iyer-Wald premise. -/
def FirstVariationNoetherOperators.omegaXY
    (D : FirstVariationNoetherOperators (L:=L) (C:=C)) :
    L →ₗ[ℝ] C :=
  -D.omegaYX

theorem FirstVariationNoetherOperators.compensated_eq_constraint
    (D : FirstVariationNoetherOperators (L:=L) (C:=C))
    (X : L) :
    D.omegaXY X + D.dB X = D.constraint X := by
  unfold FirstVariationNoetherOperators.omegaXY
  rw [D.iyerWald_identity_apply]
  module

/-- Uniqueness is therefore a theorem of the first-variation layer: no second
linear compensated current can satisfy the same derived Noether identity. -/
theorem FirstVariationNoetherOperators.omegaXY_existsUnique
    (D : FirstVariationNoetherOperators (L:=L) (C:=C)) :
    ∃! W : L →ₗ[ℝ] C,
      ∀ X : L, W X + D.dB X = D.constraint X := by
  refine ⟨D.omegaXY, D.compensated_eq_constraint, ?_⟩
  intro W hW
  ext X
  have hEq :
      W X + D.dB X = D.omegaXY X + D.dB X :=
    (hW X).trans (D.compensated_eq_constraint X).symm
  exact add_right_cancel hEq

/-- Consequently the off-shell Iyer-Wald operator identity has no independent
identity hypothesis at primitive Noether level. -/
theorem PrimitiveNoetherOperators.iyerWald_operator_identity
    (D : PrimitiveNoetherOperators (L:=L) (C:=C)) :
    D.toFirstVariationNoetherOperators.omegaYX =
      D.toFirstVariationNoetherOperators.dB -
        D.toFirstVariationNoetherOperators.constraint :=
  D.toFirstVariationNoetherOperators.iyerWald_operator_identity

/-- The compensated current is unique already at primitive Noether level. -/
theorem PrimitiveNoetherOperators.omegaXY_existsUnique
    (D : PrimitiveNoetherOperators (L:=L) (C:=C)) :
    ∃! W : L →ₗ[ℝ] C,
      ∀ X : L,
        W X + D.toFirstVariationNoetherOperators.dB X =
          D.toFirstVariationNoetherOperators.constraint X :=
  D.toFirstVariationNoetherOperators.omegaXY_existsUnique

end FirstVariationNoetherDerivation

/-! ### Lagrangian-level Iyer-Wald operator identity -/

section LagrangianIyerWaldOperator

variable {L C : Type*}
  [AddCommGroup L] [Module ℝ L]
  [AddCommGroup C] [Module ℝ C]

/-- Covariant-phase-space operators viewed as linear descendants of the Lagrangian.
The sole geometric identity retained here is the operator-level off-shell Iyer-Wald
identity.  All relative scaling, compensation, signs, and normalizations below are
derived from this one equality and the reciprocal Lagrangian jet. -/
structure LagrangianIyerWaldOperators where
  omegaYX : L →ₗ[ℝ] C
  dB : L →ₗ[ℝ] C
  constraint : L →ₗ[ℝ] C
  iw_operator_identity : omegaYX = dB - constraint

/-- Antisymmetry fixes the reversed presymplectic ordering rather than supplying
another independent current. -/
def LagrangianIyerWaldOperators.omegaXY
    (D : LagrangianIyerWaldOperators (L:=L) (C:=C)) :
    L →ₗ[ℝ] C :=
  -D.omegaYX

@[simp] theorem LagrangianIyerWaldOperators.omegaXY_apply
    (D : LagrangianIyerWaldOperators (L:=L) (C:=C))
    (X : L) :
    D.omegaXY X = -D.omegaYX X := by
  simp [LagrangianIyerWaldOperators.omegaXY]

/-- Pointwise form of the single operator-level Iyer-Wald identity. -/
theorem LagrangianIyerWaldOperators.identity_apply
    (D : LagrangianIyerWaldOperators (L:=L) (C:=C))
    (X : L) :
    D.omegaYX X = D.dB X - D.constraint X := by
  exact LinearMap.congr_fun D.iw_operator_identity X

/-- The boundary-compensated reversed current is therefore definitionally forced
to equal the constraint descendant for every Lagrangian variation. -/
theorem LagrangianIyerWaldOperators.compensated_eq_constraint
    (D : LagrangianIyerWaldOperators (L:=L) (C:=C))
    (X : L) :
    D.omegaXY X + D.dB X = D.constraint X := by
  rw [D.omegaXY_apply, D.identity_apply]
  module

/-- No second compensated current can satisfy the same Lagrangian Iyer-Wald identity. -/
theorem LagrangianIyerWaldOperators.omegaXY_unique
    (D : LagrangianIyerWaldOperators (L:=L) (C:=C))
    (W : L →ₗ[ℝ] C)
    (hW : ∀ X : L, W X + D.dB X = D.constraint X) :
    W = D.omegaXY := by
  ext X
  have hEq :
      W X + D.dB X =
        D.omegaXY X + D.dB X :=
    (hW X).trans (D.compensated_eq_constraint X).symm
  exact add_right_cancel hEq

/-- Existence and uniqueness form: the reversed presymplectic current is the unique
linear current whose boundary compensation equals the Lagrangian constraint operator. -/
theorem LagrangianIyerWaldOperators.omegaXY_existsUnique
    (D : LagrangianIyerWaldOperators (L:=L) (C:=C)) :
    ∃! W : L →ₗ[ℝ] C,
      ∀ X : L, W X + D.dB X = D.constraint X := by
  refine ⟨D.omegaXY, D.compensated_eq_constraint, ?_⟩
  intro W hW
  exact D.omegaXY_unique W hW

/-- Opposite gravity/Maxwell constraint descendants force the relative normal
constraint to be exactly `-2 ell`. -/
theorem LagrangianIyerWaldOperators.constraint_normalJet_of_opposite
    (D : LagrangianIyerWaldOperators (L:=L) (C:=C))
    (LG LM : L) (ell : C)
    (hG : D.constraint LG = ell)
    (hM : D.constraint LM = -ell) :
    D.constraint (reciprocalLagrangianNormalJet LG LM) =
      (-2 : ℝ) • ell :=
  linearDescendant_normalJet_of_opposite
    D.constraint LG LM ell hG hM

/-- The complete compensated relative-normal Iyer-Wald current follows from the
Lagrangian operator identity and opposite sector constraint values. -/
theorem LagrangianIyerWaldOperators.compensated_relative_normal
    (D : LagrangianIyerWaldOperators (L:=L) (C:=C))
    (LG LM : L) (ell : C)
    (hG : D.constraint LG = ell)
    (hM : D.constraint LM = -ell) :
    D.omegaXY (reciprocalLagrangianNormalJet LG LM) +
        D.dB (reciprocalLagrangianNormalJet LG LM) =
      (-2 : ℝ) • ell := by
  rw [D.compensated_eq_constraint]
  exact D.constraint_normalJet_of_opposite LG LM ell hG hM

end LagrangianIyerWaldOperator

/-- Forgetful constructor: the older Iyer-Wald operator package is now derived from
the stronger first-variation/Noether package rather than assumed independently. -/
def FirstVariationNoetherOperators.toLagrangianIyerWaldOperators
    {L C : Type*}
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup C] [Module ℝ C]
    (D : FirstVariationNoetherOperators (L:=L) (C:=C)) :
    LagrangianIyerWaldOperators (L:=L) (C:=C) where
  omegaYX := D.omegaYX
  dB := D.dB
  constraint := D.constraint
  iw_operator_identity := D.iyerWald_operator_identity

/-- The current obtained after forgetting to the Iyer-Wald package is definitionally
the same current already forced at first-variation level. -/
@[simp] theorem FirstVariationNoetherOperators.toIyerWald_omegaXY
    {L C : Type*}
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup C] [Module ℝ C]
    (D : FirstVariationNoetherOperators (L:=L) (C:=C)) :
    D.toLagrangianIyerWaldOperators.omegaXY = D.omegaXY := by
  ext X
  simp [FirstVariationNoetherOperators.toLagrangianIyerWaldOperators,
    LagrangianIyerWaldOperators.omegaXY,
    FirstVariationNoetherOperators.omegaXY]



/-! ### Actual first variation to Maxwell carrier current -/

section LagrangianVariationCarrierBridge

variable {L V W : Type*}
  [AddCommGroup L] [Module ℝ L]
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- The current bridge now follows from the Lagrangian first-variation equations,
without an Iyer-Wald identity premise or an intermediate Iyer-Wald structure. -/
theorem lagrangianVariation_compensated_eq_carrierBulkResponse
    (D : LagrangianVariationNoetherOperators
      (L:=L) (C:=(V →ₗ[ℝ] ℝ)))
    (LG LM : L)
    (integrate : W →ₗ[ℝ] ℝ)
    (J T : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W)
    (hJ : J = (-16 * Real.pi) • T)
    (hG : D.constraint LG = stressResponse integrate T iε)
    (hM : D.constraint LM = -(stressResponse integrate T iε)) :
    D.omegaXY (reciprocalLagrangianNormalJet LG LM) +
        D.dB (reciprocalLagrangianNormalJet LG LM) =
      carrierBulkResponse integrate J iε := by
  rw [D.compensated_relative_normal
      LG LM (stressResponse integrate T iε) hG hM,
    carrierBulkResponse_eq_minus_two_stressResponse
      integrate J T iε hJ]

/-- Consequently the manuscript's negative-half normalization is fixed directly
from first variation and the Einstein-Maxwell carrier jet. -/
theorem lagrangianVariation_half_compensated_eq_stressResponse
    (D : LagrangianVariationNoetherOperators
      (L:=L) (C:=(V →ₗ[ℝ] ℝ)))
    (LG LM : L)
    (integrate : W →ₗ[ℝ] ℝ)
    (J T : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W)
    (hJ : J = (-16 * Real.pi) • T)
    (hG : D.constraint LG = stressResponse integrate T iε)
    (hM : D.constraint LM = -(stressResponse integrate T iε)) :
    (-1 / 2 : ℝ) •
      (D.omegaXY (reciprocalLagrangianNormalJet LG LM) +
        D.dB (reciprocalLagrangianNormalJet LG LM)) =
      stressResponse integrate T iε := by
  rw [lagrangianVariation_compensated_eq_carrierBulkResponse
      D LG LM integrate J T iε hJ hG hM]
  simpa [halfCarrierBulkCurrent] using
    (halfCarrierBulkCurrent_eq_stressResponse
      integrate J T iε hJ)

end LagrangianVariationCarrierBridge

/-! ### Lagrangian operator identity to Maxwell carrier current -/

section LagrangianIyerWaldCarrierBridge

variable {L V W : Type*}
  [AddCommGroup L] [Module ℝ L]
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Once the Einstein-Maxwell constraint descendant has the opposite sector values
forced by the reciprocal Lagrangian, the Lagrangian Iyer-Wald operator identity
produces the carrier bulk current with no separate `hIW` or antisymmetry hypothesis. -/
theorem lagrangianIyerWald_compensated_eq_carrierBulkResponse
    (D : LagrangianIyerWaldOperators
      (L:=L) (C:=(V →ₗ[ℝ] ℝ)))
    (LG LM : L)
    (integrate : W →ₗ[ℝ] ℝ)
    (J T : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W)
    (hJ : J = (-16 * Real.pi) • T)
    (hG : D.constraint LG = stressResponse integrate T iε)
    (hM : D.constraint LM = -(stressResponse integrate T iε)) :
    D.omegaXY (reciprocalLagrangianNormalJet LG LM) +
        D.dB (reciprocalLagrangianNormalJet LG LM) =
      carrierBulkResponse integrate J iε := by
  rw [D.compensated_relative_normal
      LG LM (stressResponse integrate T iε) hG hM,
    carrierBulkResponse_eq_minus_two_stressResponse
      integrate J T iε hJ]

/-- Therefore the characteristic negative-half contraction is forced directly from
the Lagrangian-level Iyer-Wald identity and the Einstein-Maxwell field-equation jet. -/
theorem lagrangianIyerWald_half_compensated_eq_stressResponse
    (D : LagrangianIyerWaldOperators
      (L:=L) (C:=(V →ₗ[ℝ] ℝ)))
    (LG LM : L)
    (integrate : W →ₗ[ℝ] ℝ)
    (J T : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W)
    (hJ : J = (-16 * Real.pi) • T)
    (hG : D.constraint LG = stressResponse integrate T iε)
    (hM : D.constraint LM = -(stressResponse integrate T iε)) :
    (-1 / 2 : ℝ) •
      (D.omegaXY (reciprocalLagrangianNormalJet LG LM) +
        D.dB (reciprocalLagrangianNormalJet LG LM)) =
      stressResponse integrate T iε := by
  rw [lagrangianIyerWald_compensated_eq_carrierBulkResponse
      D LG LM integrate J T iε hJ hG hM]
  simpa [halfCarrierBulkCurrent] using
    (halfCarrierBulkCurrent_eq_stressResponse
      integrate J T iε hJ)

end LagrangianIyerWaldCarrierBridge

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

/-! ### Covector-level Iyer-Wald compensation and carrier bridge -/

section IyerWaldLinearBridge

variable {V W : Type*}
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Linear relative constraint response forced by the reciprocal fixed-point character. -/
def relativeConstraintVariation
    (ell : V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] ℝ :=
  (-2 : ℝ) • ell

@[simp] theorem relativeConstraintVariation_apply
    (ell : V →ₗ[ℝ] ℝ) (v : V) :
    relativeConstraintVariation ell v = -2 * ell v := by
  simp [relativeConstraintVariation]
  ring

/-- Pointwise, this covector is exactly the normal derivative of the reciprocal
constraint residual already proved above. -/
theorem relativeConstraintVariation_eq_residual_deriv
    (ell : V →ₗ[ℝ] ℝ) (v : V) :
    relativeConstraintVariation ell v =
      deriv (relativeConstraintResidual (ell v)) 0 := by
  rw [relativeConstraintVariation_apply,
    relativeConstraintResidual_deriv_zero]

/-- Antisymmetry and the off-shell Iyer-Wald identity force the compensated
bulk current as an equality of covectors, not merely pointwise scalars. -/
theorem iyerWald_boundary_compensation_linear
    (omegaYX omegaXY dB deltaC : V →ₗ[ℝ] ℝ)
    (hanti : omegaXY = -omegaYX)
    (hIW : omegaYX = dB - deltaC) :
    omegaXY + dB = deltaC := by
  rw [hanti, hIW]
  module

/-- If the off-shell constraint variation is the reciprocal Einstein-Maxwell response,
the compensated Iyer-Wald current is exactly `-2 ell` as a covector. -/
theorem iyerWald_bulk_response_linear
    (omegaYX omegaXY dB ell : V →ₗ[ℝ] ℝ)
    (hanti : omegaXY = -omegaYX)
    (hIW :
      omegaYX =
        dB - relativeConstraintVariation ell) :
    omegaXY + dB = relativeConstraintVariation ell := by
  exact iyerWald_boundary_compensation_linear
    omegaYX omegaXY dB
    (relativeConstraintVariation ell) hanti hIW

/-- Combining the off-shell Iyer-Wald identity with the field-equation jet
`J=-16πT` forces the compensated current to be the carrier current itself. -/
theorem iyerWald_compensated_eq_carrierBulkResponse
    (omegaYX omegaXY dB : V →ₗ[ℝ] ℝ)
    (integrate : W →ₗ[ℝ] ℝ)
    (J T : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W)
    (hJ : J = (-16 * Real.pi) • T)
    (hanti : omegaXY = -omegaYX)
    (hIW :
      omegaYX =
        dB -
          relativeConstraintVariation
            (stressResponse integrate T iε)) :
    omegaXY + dB =
      carrierBulkResponse integrate J iε := by
  rw [iyerWald_bulk_response_linear
      omegaYX omegaXY dB
      (stressResponse integrate T iε)
      hanti hIW,
    relativeConstraintVariation,
    carrierBulkResponse_eq_minus_two_stressResponse
      integrate J T iε hJ]

/-- Therefore the manuscript's characteristic half-contraction is exactly the
integrated Maxwell stress covector, with the sign and factor fixed. -/
theorem iyerWald_half_compensated_eq_stressResponse
    (omegaYX omegaXY dB : V →ₗ[ℝ] ℝ)
    (integrate : W →ₗ[ℝ] ℝ)
    (J T : V →ₗ[ℝ] V)
    (iε : V →ₗ[ℝ] W)
    (hJ : J = (-16 * Real.pi) • T)
    (hanti : omegaXY = -omegaYX)
    (hIW :
      omegaYX =
        dB -
          relativeConstraintVariation
            (stressResponse integrate T iε)) :
    (-1 / 2 : ℝ) • (omegaXY + dB) =
      stressResponse integrate T iε := by
  rw [iyerWald_compensated_eq_carrierBulkResponse
      omegaYX omegaXY dB integrate J T iε
      hJ hanti hIW]
  simpa [halfCarrierBulkCurrent] using
    (halfCarrierBulkCurrent_eq_stressResponse
      integrate J T iε hJ)

end IyerWaldLinearBridge

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

/-! ### Principal-frame local quotient and canonical timelike lift -/

/-- Canonical lift from the local stress-visible quotient to the selected timelike line. -/
def principalLocalLift :
    ((Fin 4 → ℝ) ⧸ LinearMap.ker principalTOLinear) →ₗ[ℝ]
      (Fin 4 → ℝ) :=
  (quotientClockCovector principalTOLinear).smulRight principalUhat

/-- The quotient lift acts exactly as `[v] ↦ T_O(v) û_*`. -/
theorem principalLocalLift_mk (v : Fin 4 → ℝ) :
    principalLocalLift (Submodule.Quotient.mk v) =
      principalTO v • principalUhat := by
  simp [principalLocalLift, quotientClockCovector,
    principalTOLinear_apply]

/-- Every vector differs from its lifted quotient representative by a spatial vector. -/
theorem principal_local_remainder_mem_kernel
    (v : Fin 4 → ℝ) :
    v - principalTO v • principalUhat ∈
      LinearMap.ker principalTOLinear := by
  simp [principalTOLinear, principalTO, principalUhat, principalBasis]

/-- Hence the quotient class of every vector is exactly the class of its selected
timelike representative. -/
theorem principal_quotient_eq_timelike_rep
    (v : Fin 4 → ℝ) :
    (Submodule.Quotient.mk v :
      (Fin 4 → ℝ) ⧸ LinearMap.ker principalTOLinear) =
    Submodule.Quotient.mk (principalTO v • principalUhat) := by
  exact (Submodule.Quotient.eq _).2
    (principal_local_remainder_mem_kernel v)

/-- On the selected timelike line, the quotient-lift composition is the identity. -/
theorem principalLocalLift_inverts_timelike
    (c : ℝ) :
    principalLocalLift
      (Submodule.Quotient.mk (c • principalUhat)) =
      c • principalUhat := by
  rw [principalLocalLift_mk]
  simp [principalTO_unit]

/-- The lift is a canonical section of the quotient map. -/
theorem principalLocalLift_section
    (q : (Fin 4 → ℝ) ⧸ LinearMap.ker principalTOLinear) :
    Submodule.Quotient.mk (principalLocalLift q) = q := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro v
  rw [principalLocalLift_mk]
  exact (principal_quotient_eq_timelike_rep v).symm

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

/-- Canonical symplectic reduction of a skew bilinear form by its full characteristic kernel. -/
def presymplecticReductionForm
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hskew : ∀ x y : V, B x y = - B y x) :
    (V ⧸ LinearMap.ker B) →ₗ[ℝ]
      (V ⧸ LinearMap.ker B) →ₗ[ℝ] ℝ :=
  skewQuotientBilinearForm B (LinearMap.ker B) hskew le_rfl

/-- The reduced form evaluates on quotient representatives exactly as the original form. -/
@[simp] theorem presymplecticReductionForm_mk
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hskew : ∀ x y : V, B x y = - B y x)
    (x y : V) :
    presymplecticReductionForm B hskew
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      B x y := by
  rfl

/-- Quotienting a skew presymplectic form by its entire characteristic kernel makes the
descended form left-nondegenerate. -/
theorem presymplecticReductionForm_left_nondegenerate
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hskew : ∀ x y : V, B x y = - B y x)
    (x : V ⧸ LinearMap.ker B)
    (hzero :
      ∀ y : V ⧸ LinearMap.ker B,
        presymplecticReductionForm B hskew x y = 0) :
    x = 0 := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  rw [Submodule.Quotient.mk_eq_zero]
  change B v = 0
  apply LinearMap.ext
  intro w
  simpa using hzero (Submodule.Quotient.mk w)

/-- By skew-symmetry the same reduced form is nondegenerate in the second slot as well. -/
theorem presymplecticReductionForm_right_nondegenerate
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hskew : ∀ x y : V, B x y = - B y x)
    (y : V ⧸ LinearMap.ker B)
    (hzero :
      ∀ x : V ⧸ LinearMap.ker B,
        presymplecticReductionForm B hskew x y = 0) :
    y = 0 := by
  apply presymplecticReductionForm_left_nondegenerate B hskew y
  intro x
  have hx := hzero x
  have hredskew :
      presymplecticReductionForm B hskew y x =
        - presymplecticReductionForm B hskew x y := by
    exact quotientBilinearForm_skew
      B (LinearMap.ker B) le_rfl
      (skew_right_radical_of_left B (LinearMap.ker B) hskew le_rfl)
      hskew y x
  rw [hredskew, hx, neg_zero]

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

/-! ### Exact global-to-principal-local clock identification -/

section GlobalLocalClockIso

variable {K : Type*} [AddCommGroup K] [Module ℝ K]

/-- The selected local unit is the quotient class of the normalized principal timelike vector. -/
def principalLocalQuotientUnit :
    (Fin 4 → ℝ) ⧸ LinearMap.ker principalTOLinear :=
  Submodule.Quotient.mk principalUhat

/-- The local descended clock covector evaluates to one on the selected principal unit. -/
@[simp] theorem principalLocalQuotientUnit_normalized :
    quotientClockCovector principalTOLinear
      principalLocalQuotientUnit = 1 := by
  have h :=
    LinearMap.congr_fun
      (quotientClockCovector_pullback principalTOLinear)
      principalUhat
  change
    quotientClockCovector principalTOLinear
        (Submodule.Quotient.mk principalUhat) =
      principalTOLinear principalUhat at h
  simpa [principalLocalQuotientUnit, principalTOLinear_apply,
    principalTO_unit] using h

/-- The principal local clock covector is nonzero. -/
theorem principalTOLinear_nonzero :
    principalTOLinear ≠ 0 := by
  intro h
  have hu : principalTOLinear principalUhat = 1 := by
    simpa [principalTOLinear_apply] using principalTO_unit
  rw [h] at hu
  simp at hu

/-- The principal local quotient is exactly one-dimensional. -/
theorem principalLocalQuotient_finrank_one :
    Module.finrank ℝ
      ((Fin 4 → ℝ) ⧸ LinearMap.ker principalTOLinear) = 1 :=
  clockQuotient_finrank_one principalTOLinear principalTOLinear_nonzero

/-- Globally normalized element selected by a nonzero characteristic clock covector. -/
noncomputable def globalClockQuotientUnit
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    K ⧸ LinearMap.ker Λ :=
  normalizedClockUnit
    (quotientClockCovector Λ)
    (quotientClockCovector_nonzero Λ hΛ)
    (clockQuotient_finrank_one Λ hΛ)

@[simp] theorem globalClockQuotientUnit_normalized
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    quotientClockCovector Λ
      (globalClockQuotientUnit Λ hΛ) = 1 := by
  exact normalizedClockUnit_eval
    (quotientClockCovector Λ)
    (quotientClockCovector_nonzero Λ hΛ)
    (clockQuotient_finrank_one Λ hΛ)

/-- Manuscript map
`I_{Φ,x}(X)=dΘ_Φ(X)[û_*]` from the integrated clock line to the local one. -/
def globalToPrincipalLocalClockMap
    (Λ : K →ₗ[ℝ] ℝ) :
    (K ⧸ LinearMap.ker Λ) →ₗ[ℝ]
      ((Fin 4 → ℝ) ⧸ LinearMap.ker principalTOLinear) :=
  normalizedClockMap
    (quotientClockCovector Λ)
    principalLocalQuotientUnit

@[simp] theorem globalToPrincipalLocalClockMap_apply
    (Λ : K →ₗ[ℝ] ℝ)
    (X : K ⧸ LinearMap.ker Λ) :
    globalToPrincipalLocalClockMap Λ X =
      (quotientClockCovector Λ X) •
        principalLocalQuotientUnit := rfl

/-- The local clock covector pulls back exactly to the global descended clock covector. -/
theorem globalToPrincipalLocalClockMap_pullback
    (Λ : K →ₗ[ℝ] ℝ) :
    (quotientClockCovector principalTOLinear).comp
        (globalToPrincipalLocalClockMap Λ) =
      quotientClockCovector Λ := by
  ext X
  exact normalizedClockMap_preserves_covector
    (quotientClockCovector Λ)
    (quotientClockCovector principalTOLinear)
    principalLocalQuotientUnit
    principalLocalQuotientUnit_normalized
    X

/-- For nonzero global response the clock map is automatically bijective. -/
theorem globalToPrincipalLocalClockMap_bijective
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    Function.Bijective
      (globalToPrincipalLocalClockMap Λ) := by
  exact normalizedClockMap_bijective
    (quotientClockCovector Λ)
    (quotientClockCovector principalTOLinear)
    (globalClockQuotientUnit Λ hΛ)
    principalLocalQuotientUnit
    (globalClockQuotientUnit_normalized Λ hΛ)
    principalLocalQuotientUnit_normalized
    (clockQuotient_finrank_one Λ hΛ)
    principalLocalQuotient_finrank_one

/-- The exact global/local clock isomorphism forced by covector preservation. -/
noncomputable def globalToPrincipalLocalClockEquiv
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    (K ⧸ LinearMap.ker Λ) ≃ₗ[ℝ]
      ((Fin 4 → ℝ) ⧸ LinearMap.ker principalTOLinear) :=
  LinearEquiv.ofBijective
    (globalToPrincipalLocalClockMap Λ)
    (globalToPrincipalLocalClockMap_bijective Λ hΛ)

/-- The globally normalized positive unit maps to the selected local principal unit. -/
theorem globalClockUnit_maps_to_principalUnit
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    globalToPrincipalLocalClockMap Λ
      (globalClockQuotientUnit Λ hΛ) =
        principalLocalQuotientUnit := by
  rw [globalToPrincipalLocalClockMap_apply,
    globalClockQuotientUnit_normalized, one_smul]

/-- Composing the local quotient lift with the global/local identification sends the
globally normalized unit all the way to the normalized principal timelike vector. -/
theorem normalizationBridge_principal
    (Λ : K →ₗ[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    principalLocalLift
      (globalToPrincipalLocalClockMap Λ
        (globalClockQuotientUnit Λ hΛ)) =
      principalUhat := by
  rw [globalClockUnit_maps_to_principalUnit Λ hΛ]
  change
    principalLocalLift
      (Submodule.Quotient.mk principalUhat) =
      principalUhat
  simpa using principalLocalLift_inverts_timelike (1 : ℝ)

end GlobalLocalClockIso

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


/-- The same positive response written directly in terms of the principal Maxwell field. -/
def maxwellPositiveResponseFromField
    (f E B vol : ℝ) : ℝ :=
  f * principalFieldEnergyDensity E B * vol

/-- Field and carrier expressions for the positive response are identical. -/
theorem maxwellPositiveResponseFromField_eq
    (f E B vol : ℝ) :
    maxwellPositiveResponseFromField f E B vol =
      maxwellPositiveResponse f (principalChi E B) vol := by
  unfold maxwellPositiveResponseFromField maxwellPositiveResponse
  rw [principalFieldEnergyDensity_eq_chi]
  ring

/-- Any nonzero principal Maxwell field and positive test profile gives a strictly positive
physical response. -/
theorem maxwellPositiveResponseFromField_pos
    (f E B vol : ℝ)
    (hf : 0 < f)
    (hfield : E ≠ 0 ∨ B ≠ 0)
    (hvol : 0 < vol) :
    0 < maxwellPositiveResponseFromField f E B vol := by
  rw [maxwellPositiveResponseFromField_eq]
  exact maxwellPositiveResponse_pos
    f (principalChi E B) vol hf
    (principalChi_pos E B hfield) hvol

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


/-- Intrinsic positive clock rate constructed directly from the principal Maxwell field. -/
def principalClockRate (E B : ℝ) : ℝ :=
  Real.sqrt (principalChi E B)

@[simp] theorem principalClockRate_nonneg (E B : ℝ) :
    0 ≤ principalClockRate E B :=
  Real.sqrt_nonneg _

/-- Its square is exactly the Rainich carrier. -/
theorem principalClockRate_sq (E B : ℝ) :
    (principalClockRate E B)^2 = principalChi E B := by
  unfold principalClockRate
  exact Real.sq_sqrt (principalChi_nonneg E B)

/-- The positive fourth root of the two Maxwell invariants is exactly the same clock rate. -/
theorem principalClockRate_eq_invariant_fourth_root
    (E B : ℝ) :
    principalClockRate E B =
      Real.sqrt
        (Real.sqrt
          ((maxwellI E B)^2 + (maxwellJ E B)^2)) := by
  rw [maxwell_invariants_eq_principalChi_sq,
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg (principalChi_nonneg E B)]
  rfl

/-- The same rate is fixed by the explicit principal electromagnetic energy density. -/
theorem principalClockRate_eq_energy_density
    (E B : ℝ) :
    principalClockRate E B =
      4 * Real.sqrt
        (Real.pi * principalFieldEnergyDensity E B) := by
  apply energy_density_clock_rate_value
  · unfold principalFieldEnergyDensity
    positivity
  · exact principalClockRate_nonneg E B
  · rw [principalClockRate_sq,
      principalFieldEnergyDensity_eq_chi]
    field_simp [ne_of_gt Real.pi_pos]

/-- The Ricci-norm construction from the same carrier gives the identical positive rate. -/
theorem principalClockRate_eq_ricci_fourth_root
    (E B : ℝ) :
    principalClockRate E B =
      Real.sqrt
        (Real.sqrt
          (principalRicciNormFromCarrier
            (principalChi E B))) := by
  rw [principalRicciNormFromCarrier_eq,
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg (principalChi_nonneg E B)]
  rfl

/-- All three manuscript clock normalizations coincide without an independent scale choice. -/
theorem principalClockRate_three_way
    (E B : ℝ) :
    principalClockRate E B =
        4 * Real.sqrt
          (Real.pi * principalFieldEnergyDensity E B) ∧
    principalClockRate E B =
        Real.sqrt
          (Real.sqrt
            ((maxwellI E B)^2 + (maxwellJ E B)^2)) ∧
    principalClockRate E B =
        Real.sqrt
          (Real.sqrt
            (principalRicciNormFromCarrier
              (principalChi E B))) := by
  exact ⟨principalClockRate_eq_energy_density E B,
    principalClockRate_eq_invariant_fourth_root E B,
    principalClockRate_eq_ricci_fourth_root E B⟩

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

/-! ### Accumulated intrinsic clock along the selected worldline -/

/-- Intrinsic clock accumulated from its local curvature rate. -/
def clockAccumulation (ω : ℝ → ℝ) (τ0 τ : ℝ) : ℝ :=
  ∫ s in τ0..τ, ω s

/-- A continuous intrinsic rate integrates to a clock whose derivative is exactly that rate. -/
theorem clockAccumulation_hasDerivAt
    (ω : ℝ → ℝ) (τ0 τ : ℝ)
    (hω : Continuous ω) :
    HasDerivAt (clockAccumulation ω τ0) (ω τ) τ := by
  unfold clockAccumulation
  exact intervalIntegral.integral_hasDerivAt_right
    (hω.intervalIntegrable τ0 τ)
    hω.aestronglyMeasurable.stronglyMeasurableAtFilter
    hω.continuousAt

/-- Derivative form of the intrinsic clock-rate identity. -/
theorem clockAccumulation_deriv
    (ω : ℝ → ℝ) (τ0 τ : ℝ)
    (hω : Continuous ω) :
    deriv (clockAccumulation ω τ0) τ = ω τ :=
  (clockAccumulation_hasDerivAt ω τ0 τ hω).deriv

/-- The accumulated clock has the chosen additive origin at `τ0`. -/
@[simp] theorem clockAccumulation_origin
    (ω : ℝ → ℝ) (τ0 : ℝ) :
    clockAccumulation ω τ0 τ0 = 0 := by
  simp [clockAccumulation]

/-- If the rate is positive everywhere, the accumulated clock is locally strictly increasing
where the FTC derivative is evaluated. -/
theorem clockAccumulation_deriv_pos
    (ω : ℝ → ℝ) (τ0 τ : ℝ)
    (hω : Continuous ω)
    (hpos : 0 < ω τ) :
    0 < deriv (clockAccumulation ω τ0) τ := by
  rw [clockAccumulation_deriv ω τ0 τ hω]
  exact hpos

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


/-! ### Adapted-frame derivation of the chronometric transport two-form -/

/-- Covariant components of the normalized timelike covector in an adapted orthonormal frame. -/
def principalUFlat (i : Fin 4) : ℝ :=
  if i = 0 then -1 else 0

/-- Pointwise component expansion of
`dT_O = -d(ω u^♭)`, with `du_ab` standing for `∇_a u_b`. -/
def clockTransportTwoForm
    (ω : ℝ) (dω : Fin 4 → ℝ)
    (du : Fin 4 → Fin 4 → ℝ)
    (i j : Fin 4) : ℝ :=
  -(dω i * principalUFlat j + ω * du i j
    - dω j * principalUFlat i - ω * du j i)

/-- The transport tensor is antisymmetric by construction. -/
theorem clockTransportTwoForm_skew
    (ω : ℝ) (dω : Fin 4 → ℝ)
    (du : Fin 4 → Fin 4 → ℝ)
    (i j : Fin 4) :
    clockTransportTwoForm ω dω du i j =
      - clockTransportTwoForm ω dω du j i := by
  unfold clockTransportTwoForm
  ring

/-- Spatial vorticity components in the adapted frame. -/
def principalVorticity
    (du : Fin 4 → Fin 4 → ℝ)
    (i j : Fin 3) : ℝ :=
  (du i.succ j.succ - du j.succ i.succ) / 2

/-- Proper acceleration components in the adapted frame. -/
def principalAcceleration
    (du : Fin 4 → Fin 4 → ℝ)
    (i : Fin 3) : ℝ :=
  du 0 i.succ

/-- Unit normalization `u^b∇_a u_b=0` means the derivative of the time covector
component vanishes in spatial directions in the adapted frame. -/
def adaptedUnitNormalization
    (du : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ i : Fin 3, du i.succ 0 = 0

/-- The purely spatial transport curvature is forced to be `-2ω varpi`. -/
theorem clockTransport_spatial
    (ω : ℝ) (dω : Fin 4 → ℝ)
    (du : Fin 4 → Fin 4 → ℝ)
    (i j : Fin 3) :
    clockTransportTwoForm ω dω du i.succ j.succ =
      -2 * ω * principalVorticity du i j := by
  unfold clockTransportTwoForm principalUFlat principalVorticity
  have hi : (i.succ : Fin 4) ≠ 0 := Fin.succ_ne_zero i
  have hj : (j.succ : Fin 4) ≠ 0 := Fin.succ_ne_zero j
  simp [hi, hj]
  ring

/-- The mixed time-space component is forced by acceleration and the spatial rate gradient. -/
theorem clockTransport_mixed
    (ω : ℝ) (dω : Fin 4 → ℝ)
    (du : Fin 4 → Fin 4 → ℝ)
    (hunit : adaptedUnitNormalization du)
    (i : Fin 3) :
    clockTransportTwoForm ω dω du 0 i.succ =
      -ω * principalAcceleration du i - dω i.succ := by
  unfold clockTransportTwoForm principalUFlat principalAcceleration
  have hi : (i.succ : Fin 4) ≠ 0 := Fin.succ_ne_zero i
  have hnorm := hunit i
  simp [hi, hnorm]
  ring

/-- Using `K=ω⁴`, the mixed component is exactly the manuscript's
`-ω(a_i + 1/4 D_i log K)`. -/
theorem clockTransport_mixed_logK
    (ω : ℝ) (dω dlogK : Fin 4 → ℝ)
    (du : Fin 4 → Fin 4 → ℝ)
    (hω : ω ≠ 0)
    (hunit : adaptedUnitNormalization du)
    (hlog :
      ∀ i : Fin 3,
        dlogK i.succ = 4 * dω i.succ / ω)
    (i : Fin 3) :
    clockTransportTwoForm ω dω du 0 i.succ =
      -ω * (principalAcceleration du i +
        dlogK i.succ / 4) := by
  rw [clockTransport_mixed ω dω du hunit i]
  have hrate :=
    logarithmic_rate_coefficient
      ω (dlogK i.succ) (dω i.succ) hω (hlog i)
  rw [hrate]
  ring

/-- The spatial Frobenius component `T_O ∧ dT_O` is proportional to
`ω² varpi`; therefore no independent obstruction exists. -/
def principalFrobeniusSpatialComponent
    (ω : ℝ) (dω : Fin 4 → ℝ)
    (du : Fin 4 → Fin 4 → ℝ)
    (i j : Fin 3) : ℝ :=
  ω * clockTransportTwoForm ω dω du i.succ j.succ

theorem principalFrobeniusSpatialComponent_eq
    (ω : ℝ) (dω : Fin 4 → ℝ)
    (du : Fin 4 → Fin 4 → ℝ)
    (i j : Fin 3) :
    principalFrobeniusSpatialComponent ω dω du i j =
      -2 * ω^2 * principalVorticity du i j := by
  rw [principalFrobeniusSpatialComponent, clockTransport_spatial]
  ring

/-- On the positive/nonzero-rate sector, a spatial Frobenius component vanishes exactly
when the corresponding vorticity component vanishes. -/
theorem principalFrobeniusSpatialComponent_zero_iff
    (ω : ℝ) (dω : Fin 4 → ℝ)
    (du : Fin 4 → Fin 4 → ℝ)
    (i j : Fin 3)
    (hω : ω ≠ 0) :
    principalFrobeniusSpatialComponent ω dω du i j = 0 ↔
      principalVorticity du i j = 0 := by
  rw [principalFrobeniusSpatialComponent_eq]
  have hcoef : -2 * ω^2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hω)
  exact mul_eq_zero_iff_left hcoef


/-- Vanishing of all projected transport components is exactly the paper's acceleration/
vorticity balance, once the rate is nonzero and `K=ω⁴` supplies the logarithmic gradient. -/
theorem clockTransport_projected_zero_iff
    (ω : ℝ) (dω dlogK : Fin 4 → ℝ)
    (du : Fin 4 → Fin 4 → ℝ)
    (hω : ω ≠ 0)
    (hunit : adaptedUnitNormalization du)
    (hlog :
      ∀ i : Fin 3,
        dlogK i.succ = 4 * dω i.succ / ω) :
    ((∀ i j : Fin 3,
        clockTransportTwoForm ω dω du i.succ j.succ = 0) ∧
      (∀ i : Fin 3,
        clockTransportTwoForm ω dω du 0 i.succ = 0)) ↔
    ((∀ i j : Fin 3, principalVorticity du i j = 0) ∧
      (∀ i : Fin 3,
        principalAcceleration du i =
          -dlogK i.succ / 4)) := by
  constructor
  · rintro ⟨hsp, hmix⟩
    constructor
    · intro i j
      have h := hsp i j
      rw [clockTransport_spatial] at h
      have hcoef : -2 * ω ≠ 0 :=
        mul_ne_zero (by norm_num) hω
      exact (mul_eq_zero.mp h).resolve_left hcoef
    · intro i
      have h := hmix i
      rw [clockTransport_mixed_logK
        ω dω dlogK du hω hunit hlog i] at h
      have hs :
          principalAcceleration du i +
            dlogK i.succ / 4 = 0 :=
        (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr hω)
      linarith
  · rintro ⟨hsp, hmix⟩
    constructor
    · intro i j
      rw [clockTransport_spatial, hsp i j]
      ring
    · intro i
      rw [clockTransport_mixed_logK
        ω dω dlogK du hω hunit hlog i, hmix i]
      ring

/-- The weaker Frobenius condition on all spatial components is exactly vanishing
vorticity, with no acceleration condition. -/
theorem principalFrobenius_all_zero_iff
    (ω : ℝ) (dω : Fin 4 → ℝ)
    (du : Fin 4 → Fin 4 → ℝ)
    (hω : ω ≠ 0) :
    (∀ i j : Fin 3,
      principalFrobeniusSpatialComponent ω dω du i j = 0) ↔
    (∀ i j : Fin 3,
      principalVorticity du i j = 0) := by
  constructor
  · intro h i j
    exact (principalFrobeniusSpatialComponent_zero_iff
      ω dω du i j hω).1 (h i j)
  · intro h i j
    exact (principalFrobeniusSpatialComponent_zero_iff
      ω dω du i j hω).2 (h i j)

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

/-! ### Endpoint-integrated radar clock -/

/-- Clock reading assigned to an endpoint parameter by integrating the intrinsic local rate. -/
def endpointClock
    (ω : ℝ → ℝ) (τ0 : ℝ) (τend : ℝ → ℝ) (x : ℝ) : ℝ :=
  clockAccumulation ω τ0 (τend x)

/-- Endpoint differentiation is forced by FTC plus the chain rule:
`dΘ = ω(τ_end) dτ_end`. -/
theorem endpointClock_hasDerivAt
    (ω τend : ℝ → ℝ) (τ0 x dτ : ℝ)
    (hω : Continuous ω)
    (hend : HasDerivAt τend dτ x) :
    HasDerivAt
      (endpointClock ω τ0 τend)
      (ω (τend x) * dτ) x := by
  unfold endpointClock
  exact (clockAccumulation_hasDerivAt
    ω τ0 (τend x) hω).comp x hend

/-- Derivative form of the endpoint clock identity. -/
theorem endpointClock_deriv
    (ω τend : ℝ → ℝ) (τ0 x dτ : ℝ)
    (hω : Continuous ω)
    (hend : HasDerivAt τend dτ x) :
    deriv (endpointClock ω τ0 τend) x =
      ω (τend x) * dτ :=
  (endpointClock_hasDerivAt ω τend τ0 x dτ hω hend).deriv

/-- Exchange-even radar midpoint. -/
def radarTime (θplus θminus : ℝ) : ℝ := (θplus + θminus) / 2

/-- Exchange-odd radar defect. -/
def radarRadius (θplus θminus : ℝ) : ℝ := (θplus - θminus) / 2


/-- Spacetime radar clock obtained by integrating the same local rate to the future and
past endpoint parameters and taking the exchange-even midpoint. -/
def radarClockTime
    (ω : ℝ → ℝ) (τ0 : ℝ)
    (τplus τminus : ℝ → ℝ) (x : ℝ) : ℝ :=
  radarTime
    (endpointClock ω τ0 τplus x)
    (endpointClock ω τ0 τminus x)

/-- Exchange-odd synchronized radial reading from the same endpoint clocks. -/
def radarClockRadius
    (ω : ℝ → ℝ) (τ0 : ℝ)
    (τplus τminus : ℝ → ℝ) (x : ℝ) : ℝ :=
  radarRadius
    (endpointClock ω τ0 τplus x)
    (endpointClock ω τ0 τminus x)

/-- Derivative of the exchange-even radar clock midpoint. -/
theorem radarClockTime_hasDerivAt
    (ω τplus τminus : ℝ → ℝ)
    (τ0 x dplus dminus : ℝ)
    (hω : Continuous ω)
    (hp : HasDerivAt τplus dplus x)
    (hm : HasDerivAt τminus dminus x) :
    HasDerivAt
      (radarClockTime ω τ0 τplus τminus)
      ((ω (τplus x) * dplus +
        ω (τminus x) * dminus) / 2) x := by
  have hp' := endpointClock_hasDerivAt
    ω τplus τ0 x dplus hω hp
  have hm' := endpointClock_hasDerivAt
    ω τminus τ0 x dminus hω hm
  unfold radarClockTime radarTime
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (hp'.add hm').const_mul (1 / 2 : ℝ)

/-- Derivative of the exchange-odd radar radius. -/
theorem radarClockRadius_hasDerivAt
    (ω τplus τminus : ℝ → ℝ)
    (τ0 x dplus dminus : ℝ)
    (hω : Continuous ω)
    (hp : HasDerivAt τplus dplus x)
    (hm : HasDerivAt τminus dminus x) :
    HasDerivAt
      (radarClockRadius ω τ0 τplus τminus)
      ((ω (τplus x) * dplus -
        ω (τminus x) * dminus) / 2) x := by
  have hp' := endpointClock_hasDerivAt
    ω τplus τ0 x dplus hω hp
  have hm' := endpointClock_hasDerivAt
    ω τminus τ0 x dminus hω hm
  unfold radarClockRadius radarRadius
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (hp'.sub hm').const_mul (1 / 2 : ℝ)

/-- On the generating orbit, coincident endpoint parameters force zero synchronized radius. -/
theorem radarClockRadius_zero_of_coincident_endpoint
    (ω : ℝ → ℝ) (τ0 τ : ℝ)
    (τplus τminus : ℝ → ℝ) (x : ℝ)
    (hcoinc : τplus x = τminus x) :
    radarClockRadius ω τ0 τplus τminus x = 0 := by
  unfold radarClockRadius radarRadius endpointClock
  rw [hcoinc]
  ring

/-- At a coincident endpoint with positive nonzero rate, opposite normalized endpoint
variations give unit radial first jet. -/
theorem radarClockRadius_unit_radial_jet
    (ω τplus τminus : ℝ → ℝ)
    (τ0 x τ : ℝ)
    (hω : Continuous ω)
    (hcoincp : τplus x = τ)
    (hcoincm : τminus x = τ)
    (hrate : ω τ ≠ 0)
    (hp : HasDerivAt τplus (ω τ)⁻¹ x)
    (hm : HasDerivAt τminus (-(ω τ)⁻¹) x) :
    HasDerivAt
      (radarClockRadius ω τ0 τplus τminus)
      1 x := by
  have h :=
    radarClockRadius_hasDerivAt
      ω τplus τminus τ0 x
      (ω τ)⁻¹ (-(ω τ)⁻¹) hω hp hm
  rw [hcoincp, hcoincm] at h
  convert h using 1
  field_simp [hrate]

/-- Equal normalized endpoint variations give unit clock first jet and zero radial first jet. -/
theorem radarClockTime_unit_clock_jet
    (ω τplus τminus : ℝ → ℝ)
    (τ0 x τ : ℝ)
    (hω : Continuous ω)
    (hcoincp : τplus x = τ)
    (hcoincm : τminus x = τ)
    (hrate : ω τ ≠ 0)
    (hp : HasDerivAt τplus (ω τ)⁻¹ x)
    (hm : HasDerivAt τminus (ω τ)⁻¹ x) :
    HasDerivAt
      (radarClockTime ω τ0 τplus τminus)
      1 x := by
  have h :=
    radarClockTime_hasDerivAt
      ω τplus τminus τ0 x
      (ω τ)⁻¹ (ω τ)⁻¹ hω hp hm
  rw [hcoincp, hcoincm] at h
  convert h using 1
  field_simp [hrate]

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

/-! ### Regular Synge endpoint maps from the implicit-function theorem -/

section SyngeImplicitEndpoint

variable {X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The regular null-endpoint map is not chosen: it is the implicit function attached
to the world-function equation near a point where the endpoint partial derivative is invertible. -/
noncomputable def syngeImplicitEndpoint
    {σ : X × ℝ → ℝ}
    {u : X × ℝ}
    {Dσ : X × ℝ →L[ℝ] ℝ}
    (hσ : HasStrictFDerivAt σ Dσ u)
    (hθ : (Dσ ∘L ContinuousLinearMap.inr ℝ X ℝ).IsInvertible) :
    X → ℝ :=
  hσ.implicitFunctionOfProdDomain hθ

/-- Near the regular endpoint, solving the world-function level equation is equivalent
to lying on the constructed endpoint graph.  This is local uniqueness. -/
theorem syngeImplicitEndpoint_eventually_eq_iff
    {σ : X × ℝ → ℝ}
    {u : X × ℝ}
    {Dσ : X × ℝ →L[ℝ] ℝ}
    (hσ : HasStrictFDerivAt σ Dσ u)
    (hθ : (Dσ ∘L ContinuousLinearMap.inr ℝ X ℝ).IsInvertible) :
    ∀ᶠ v in 𝓝 u,
      σ v = σ u ↔
        syngeImplicitEndpoint hσ hθ v.1 = v.2 := by
  exact hσ.eventually_apply_eq_iff_implicitFunctionOfProdDomain hθ

/-- The constructed endpoint graph actually solves the same world-function level
equation in a neighborhood of the base spacetime point. -/
theorem syngeImplicitEndpoint_eventually_solves
    {σ : X × ℝ → ℝ}
    {u : X × ℝ}
    {Dσ : X × ℝ →L[ℝ] ℝ}
    (hσ : HasStrictFDerivAt σ Dσ u)
    (hθ : (Dσ ∘L ContinuousLinearMap.inr ℝ X ℝ).IsInvertible) :
    ∀ᶠ x in 𝓝 u.1,
      σ (x, syngeImplicitEndpoint hσ hθ x) = σ u := by
  exact hσ.eventually_apply_implicitFunctionOfProdDomain hθ

/-- Its derivative is forced by the implicit-function theorem:
`Dθ = -(D_θσ)⁻¹ ∘ D_xσ`. -/
theorem syngeImplicitEndpoint_hasStrictFDerivAt
    {σ : X × ℝ → ℝ}
    {u : X × ℝ}
    {Dσ : X × ℝ →L[ℝ] ℝ}
    (hσ : HasStrictFDerivAt σ Dσ u)
    (hθ : (Dσ ∘L ContinuousLinearMap.inr ℝ X ℝ).IsInvertible) :
    HasStrictFDerivAt
      (syngeImplicitEndpoint hσ hθ)
      (-((Dσ ∘L ContinuousLinearMap.inr ℝ X ℝ).inverse) ∘L
        (Dσ ∘L ContinuousLinearMap.inl ℝ X ℝ))
      u.1 := by
  exact hσ.hasStrictFDerivAt_implicitFunctionOfProdDomain hθ

/-- In particular the regular endpoint map is continuous at the base point. -/
theorem syngeImplicitEndpoint_continuousAt
    {σ : X × ℝ → ℝ}
    {u : X × ℝ}
    {Dσ : X × ℝ →L[ℝ] ℝ}
    (hσ : HasStrictFDerivAt σ Dσ u)
    (hθ : (Dσ ∘L ContinuousLinearMap.inr ℝ X ℝ).IsInvertible) :
    ContinuousAt (syngeImplicitEndpoint hσ hθ) u.1 :=
  (syngeImplicitEndpoint_hasStrictFDerivAt hσ hθ).continuousAt

/-- The endpoint map tends to the distinguished endpoint value itself. -/
theorem syngeImplicitEndpoint_tendsto
    {σ : X × ℝ → ℝ}
    {u : X × ℝ}
    {Dσ : X × ℝ →L[ℝ] ℝ}
    (hσ : HasStrictFDerivAt σ Dσ u)
    (hθ : (Dσ ∘L ContinuousLinearMap.inr ℝ X ℝ).IsInvertible) :
    Tendsto (syngeImplicitEndpoint hσ hθ) (𝓝 u.1) (𝓝 u.2) := by
  exact hσ.tendsto_implicitFunctionOfProdDomain hθ

end SyngeImplicitEndpoint

/-! ### Minimal Synge endpoint interface and forced optical closure -/

/-- Minimal first-jet Synge data at the two null endpoints.  The endpoint covectors
`dΘ_±`, their linearized equations, and their nullness are *not* input data.  The
only geometric facts retained are: the world function vanishes at each endpoint,
its Hamilton-Jacobi identity holds there, and the endpoint derivative is nonzero so
the implicit endpoint is regular. -/
structure SyngeEndpointJetData where
  sigmaPlus : ℝ
  sigmaMinus : ℝ
  sigmaXPlus : W
  sigmaXMinus : W
  sigmaThetaPlus : ℝ
  sigmaThetaMinus : ℝ
  endpointPlus : sigmaPlus = 0
  endpointMinus : sigmaMinus = 0
  worldEikonalPlus :
    bil B sigmaXPlus sigmaXPlus = 2 * sigmaPlus
  worldEikonalMinus :
    bil B sigmaXMinus sigmaXMinus = 2 * sigmaMinus
  sigmaThetaPlus_ne : sigmaThetaPlus ≠ 0
  sigmaThetaMinus_ne : sigmaThetaMinus ≠ 0

/-- The implicit-function theorem can only produce this endpoint covector. -/
def SyngeEndpointJetData.dThetaPlus
    (D : SyngeEndpointJetData B) : W :=
  (-D.sigmaThetaPlus⁻¹) • D.sigmaXPlus

def SyngeEndpointJetData.dThetaMinus
    (D : SyngeEndpointJetData B) : W :=
  (-D.sigmaThetaMinus⁻¹) • D.sigmaXMinus

/-- The constructed future endpoint covector solves the differentiated endpoint equation. -/
theorem SyngeEndpointJetData.linearizedPlus
    (D : SyngeEndpointJetData B) :
    D.sigmaXPlus +
      D.sigmaThetaPlus • D.dThetaPlus = 0 := by
  unfold SyngeEndpointJetData.dThetaPlus
  rw [smul_smul]
  have hcoef :
      D.sigmaThetaPlus * (-D.sigmaThetaPlus⁻¹) = -1 := by
    field_simp [D.sigmaThetaPlus_ne]
  rw [hcoef, neg_one_smul, add_neg_cancel]

/-- The constructed past endpoint covector solves the differentiated endpoint equation. -/
theorem SyngeEndpointJetData.linearizedMinus
    (D : SyngeEndpointJetData B) :
    D.sigmaXMinus +
      D.sigmaThetaMinus • D.dThetaMinus = 0 := by
  unfold SyngeEndpointJetData.dThetaMinus
  rw [smul_smul]
  have hcoef :
      D.sigmaThetaMinus * (-D.sigmaThetaMinus⁻¹) = -1 := by
    field_simp [D.sigmaThetaMinus_ne]
  rw [hcoef, neg_one_smul, add_neg_cancel]

/-- Regularity makes the future Synge endpoint covector unique: every solution of the
linearized endpoint equation is the constructed endpoint differential. -/
theorem SyngeEndpointJetData.dThetaPlus_unique
    (D : SyngeEndpointJetData B)
    (eta : W)
    (heta : D.sigmaXPlus + D.sigmaThetaPlus • eta = 0) :
    eta = D.dThetaPlus := by
  simpa [SyngeEndpointJetData.dThetaPlus] using
    (implicit_endpoint_covector
      D.sigmaXPlus eta D.sigmaThetaPlus
      D.sigmaThetaPlus_ne heta)

/-- Regularity likewise makes the past Synge endpoint covector unique. -/
theorem SyngeEndpointJetData.dThetaMinus_unique
    (D : SyngeEndpointJetData B)
    (eta : W)
    (heta : D.sigmaXMinus + D.sigmaThetaMinus • eta = 0) :
    eta = D.dThetaMinus := by
  simpa [SyngeEndpointJetData.dThetaMinus] using
    (implicit_endpoint_covector
      D.sigmaXMinus eta D.sigmaThetaMinus
      D.sigmaThetaMinus_ne heta)

/-- Synge's Hamilton-Jacobi identity plus the null endpoint condition forces the
world-function covector itself to be null. -/
theorem SyngeEndpointJetData.sigmaXPlus_null
    (D : SyngeEndpointJetData B) :
    bil B D.sigmaXPlus D.sigmaXPlus = 0 := by
  rw [D.worldEikonalPlus, D.endpointPlus]
  ring

theorem SyngeEndpointJetData.sigmaXMinus_null
    (D : SyngeEndpointJetData B) :
    bil B D.sigmaXMinus D.sigmaXMinus = 0 := by
  rw [D.worldEikonalMinus, D.endpointMinus]
  ring

/-- Therefore both implicit endpoint covectors are forced null eikonals. -/
theorem SyngeEndpointJetData.endpoint_eikonals_null
    (D : SyngeEndpointJetData B) :
    bil B D.dThetaPlus D.dThetaPlus = 0 ∧
    bil B D.dThetaMinus D.dThetaMinus = 0 := by
  constructor
  · exact implicit_endpoint_covector_null
      B D.sigmaXPlus D.dThetaPlus D.sigmaThetaPlus
      D.sigmaThetaPlus_ne D.linearizedPlus D.sigmaXPlus_null
  · exact implicit_endpoint_covector_null
      B D.sigmaXMinus D.dThetaMinus D.sigmaThetaMinus
      D.sigmaThetaMinus_ne D.linearizedMinus D.sigmaXMinus_null

/-- Exchange-even midpoint of two endpoint covectors. -/
def endpointMidpointCovector (dPlus dMinus : W) : W :=
  (1 / 2 : ℝ) • (dPlus + dMinus)

/-- Exchange-odd half-difference of the endpoint covectors. -/
def endpointRadialCovector (dPlus dMinus : W) : W :=
  (1 / 2 : ℝ) • (dPlus - dMinus)

/-- The midpoint/half-difference reconstruct the endpoint covectors exactly. -/
theorem endpointCovector_reconstruction
    (dPlus dMinus : W) :
    endpointMidpointCovector dPlus dMinus +
        endpointRadialCovector dPlus dMinus = dPlus ∧
    endpointMidpointCovector dPlus dMinus -
        endpointRadialCovector dPlus dMinus = dMinus := by
  constructor <;>
    simp [endpointMidpointCovector, endpointRadialCovector] <;>
    module

/-- The midpoint/radial decomposition is the unique pair reconstructing two endpoint
covectors. Hence no independent optical split survives once the endpoints are fixed. -/
theorem endpointCovector_decomposition_unique
    (dPlus dMinus T R : W)
    (hplus : T + R = dPlus)
    (hminus : T - R = dMinus) :
    T = endpointMidpointCovector dPlus dMinus ∧
    R = endpointRadialCovector dPlus dMinus := by
  constructor
  · unfold endpointMidpointCovector
    rw [← hplus, ← hminus]
    module
  · unfold endpointRadialCovector
    rw [← hplus, ← hminus]
    module

/-- The only smooth local Synge data needed for the optical closure: each endpoint solves
its linearized world-function equation, the endpoint derivative is nonzero, and the
world-function covector is null. -/
structure NullEndpointPairData where
  sigmaXPlus : W
  sigmaXMinus : W
  dThetaPlus : W
  dThetaMinus : W
  sigmaThetaPlus : ℝ
  sigmaThetaMinus : ℝ
  sigmaThetaPlus_ne : sigmaThetaPlus ≠ 0
  sigmaThetaMinus_ne : sigmaThetaMinus ≠ 0
  linearizedPlus :
    sigmaXPlus + sigmaThetaPlus • dThetaPlus = 0
  linearizedMinus :
    sigmaXMinus + sigmaThetaMinus • dThetaMinus = 0
  sigmaXPlus_null :
    bil B sigmaXPlus sigmaXPlus = 0
  sigmaXMinus_null :
    bil B sigmaXMinus sigmaXMinus = 0

/-- Both endpoint differentials are therefore null eikonals. -/
theorem NullEndpointPairData.endpoint_eikonals_null
    (D : NullEndpointPairData B) :
    bil B D.dThetaPlus D.dThetaPlus = 0 ∧
    bil B D.dThetaMinus D.dThetaMinus = 0 := by
  constructor
  · exact implicit_endpoint_covector_null
      B D.sigmaXPlus D.dThetaPlus D.sigmaThetaPlus
      D.sigmaThetaPlus_ne D.linearizedPlus
      D.sigmaXPlus_null
  · exact implicit_endpoint_covector_null
      B D.sigmaXMinus D.dThetaMinus D.sigmaThetaMinus
      D.sigmaThetaMinus_ne D.linearizedMinus
      D.sigmaXMinus_null

/-- Radar clock covector forced by the two endpoint eikonals. -/
def NullEndpointPairData.clockCovector
    (D : NullEndpointPairData B) : W :=
  endpointMidpointCovector D.dThetaPlus D.dThetaMinus

/-- Radar radial covector forced by the same endpoint eikonals. -/
def NullEndpointPairData.radialCovector
    (D : NullEndpointPairData B) : W :=
  endpointRadialCovector D.dThetaPlus D.dThetaMinus

/-- The endpoint eikonals are exactly clock plus/minus radial covectors. -/
theorem NullEndpointPairData.reconstruction
    (D : NullEndpointPairData B) :
    D.clockCovector + D.radialCovector = D.dThetaPlus ∧
    D.clockCovector - D.radialCovector = D.dThetaMinus :=
  endpointCovector_reconstruction D.dThetaPlus D.dThetaMinus

/-- The full optical closure follows from the minimal Synge data and symmetry of the
inverse metric: clock and radius are orthogonal and have equal-and-opposite norm. -/
theorem NullEndpointPairData.optical_closure
    (D : NullEndpointPairData B)
    (hsym : ∀ x y, bil B x y = bil B y x) :
    bil B D.clockCovector D.radialCovector = 0 ∧
    -(bil B D.clockCovector D.clockCovector) =
      bil B D.radialCovector D.radialCovector := by
  rcases D.endpoint_eikonals_null with ⟨hp, hm⟩
  rcases D.reconstruction with ⟨hrp, hrm⟩
  apply (null_pair_closure_iff B hsym
    D.clockCovector D.radialCovector).1
  constructor
  · rw [hrp]
    exact hp
  · rw [hrm]
    exact hm


/-- The older endpoint-pair interface is canonically reconstructed from the minimal
Synge world-function jet data. -/
def SyngeEndpointJetData.toNullEndpointPairData
    (D : SyngeEndpointJetData B) :
    NullEndpointPairData B where
  sigmaXPlus := D.sigmaXPlus
  sigmaXMinus := D.sigmaXMinus
  dThetaPlus := D.dThetaPlus
  dThetaMinus := D.dThetaMinus
  sigmaThetaPlus := D.sigmaThetaPlus
  sigmaThetaMinus := D.sigmaThetaMinus
  sigmaThetaPlus_ne := D.sigmaThetaPlus_ne
  sigmaThetaMinus_ne := D.sigmaThetaMinus_ne
  linearizedPlus := D.linearizedPlus
  linearizedMinus := D.linearizedMinus
  sigmaXPlus_null := D.sigmaXPlus_null
  sigmaXMinus_null := D.sigmaXMinus_null

/-- Radar clock covector constructed directly from the minimal Synge jet. -/
def SyngeEndpointJetData.clockCovector
    (D : SyngeEndpointJetData B) : W :=
  endpointMidpointCovector D.dThetaPlus D.dThetaMinus

/-- Radar radial covector constructed directly from the same minimal Synge jet. -/
def SyngeEndpointJetData.radialCovector
    (D : SyngeEndpointJetData B) : W :=
  endpointRadialCovector D.dThetaPlus D.dThetaMinus

/-- The smooth Synge clock/radius covectors are unique, not merely canonically defined. -/
theorem SyngeEndpointJetData.clock_radial_unique
    (D : SyngeEndpointJetData B)
    (T R : W)
    (hplus : T + R = D.dThetaPlus)
    (hminus : T - R = D.dThetaMinus) :
    T = D.clockCovector ∧ R = D.radialCovector := by
  simpa [SyngeEndpointJetData.clockCovector,
    SyngeEndpointJetData.radialCovector] using
    (endpointCovector_decomposition_unique
      D.dThetaPlus D.dThetaMinus T R hplus hminus)

/-- Full first-jet uniqueness certificate: every regular candidate endpoint pair and
every clock/radius split satisfying the defining equations is the Synge-derived one. -/
theorem SyngeEndpointJetData.firstJet_forced_unique
    (D : SyngeEndpointJetData B)
    (dPlus dMinus T R : W)
    (hlinPlus : D.sigmaXPlus + D.sigmaThetaPlus • dPlus = 0)
    (hlinMinus : D.sigmaXMinus + D.sigmaThetaMinus • dMinus = 0)
    (hplus : T + R = dPlus)
    (hminus : T - R = dMinus) :
    dPlus = D.dThetaPlus ∧
    dMinus = D.dThetaMinus ∧
    T = D.clockCovector ∧
    R = D.radialCovector := by
  have hp : dPlus = D.dThetaPlus :=
    D.dThetaPlus_unique dPlus hlinPlus
  have hm : dMinus = D.dThetaMinus :=
    D.dThetaMinus_unique dMinus hlinMinus
  rw [hp] at hplus
  rw [hm] at hminus
  rcases D.clock_radial_unique T R hplus hminus with ⟨hT, hR⟩
  exact ⟨hp, hm, hT, hR⟩

/-- The complete optical closure is forced directly from the world-function endpoint
condition, Synge Hamilton-Jacobi identity, and regular implicit endpoint derivative. -/
theorem SyngeEndpointJetData.optical_closure
    (D : SyngeEndpointJetData B)
    (hsym : ∀ x y, bil B x y = bil B y x) :
    bil B D.clockCovector D.radialCovector = 0 ∧
    -(bil B D.clockCovector D.clockCovector) =
      bil B D.radialCovector D.radialCovector := by
  have h :=
    D.toNullEndpointPairData.optical_closure hsym
  simpa [SyngeEndpointJetData.clockCovector,
    SyngeEndpointJetData.radialCovector,
    NullEndpointPairData.clockCovector,
    NullEndpointPairData.radialCovector,
    SyngeEndpointJetData.toNullEndpointPairData] using h

/-- Thus the optical lapse norm is not independent endpoint data: the two norms are the
same scalar with opposite sign. -/
theorem NullEndpointPairData.equal_norm_forced
    (D : NullEndpointPairData B)
    (hsym : ∀ x y, bil B x y = bil B y x) :
    bil B D.radialCovector D.radialCovector =
      -(bil B D.clockCovector D.clockCovector) :=
  (D.optical_closure hsym).2.symm

end OpticalClosure

/-! ### Exact two-dimensional optical metric reconstruction -/

/-- In the `(dT,dR)` basis, the inverse optical metric has common magnitude `q=N_opt⁻²`. -/
def opticalInverseMetric2 (q : ℝ) (x y : R2) : ℝ :=
  q * (-x.1 * y.1 + x.2 * y.2)

/-- The corresponding covariant optical metric is forced to carry reciprocal magnitude
`q⁻¹=N_opt²`. -/
def opticalMetric2 (q : ℝ) (x y : R2) : ℝ :=
  q⁻¹ * (-x.1 * y.1 + x.2 * y.2)

/-- Matrix coefficient of the inverse optical metric. -/
def opticalInverseMetric2Matrix (q : ℝ) (i j : Fin 2) : ℝ :=
  if i = j then if i = 0 then -q else q else 0

/-- Matrix coefficient of the covariant optical metric. -/
def opticalMetric2Matrix (q : ℝ) (i j : Fin 2) : ℝ :=
  if i = j then if i = 0 then -q⁻¹ else q⁻¹ else 0

/-- The reconstructed covariant and contravariant optical metrics are exact matrix inverses
whenever the common endpoint norm is nonzero. -/
theorem opticalMetric2_inverse
    (q : ℝ) (hq : q ≠ 0) (i j : Fin 2) :
    (∑ k : Fin 2,
      opticalMetric2Matrix q i k *
        opticalInverseMetric2Matrix q k j) =
      (if i = j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;>
    simp [opticalMetric2Matrix, opticalInverseMetric2Matrix, hq]

/-- The clock and radial basis covectors have equal-and-opposite inverse norms `-q,+q`. -/
theorem opticalInverseMetric2_basis_norms (q : ℝ) :
    opticalInverseMetric2 q TO TO = -q ∧
    opticalInverseMetric2 q RO RO = q ∧
    opticalInverseMetric2 q TO RO = 0 := by
  constructor
  · simp [opticalInverseMetric2, TO]
  · constructor <;> simp [opticalInverseMetric2, TO, RO]

/-- Thus if `q=N_opt⁻²`, the covariant metric is literally
`N_opt²(-dT²+dR²)`. -/
theorem opticalMetric2_lapse_form
    (N q : ℝ)
    (hN : N ≠ 0)
    (hq : q = N⁻²) :
    ∀ x y : R2,
      opticalMetric2 q x y =
        N^2 * (-x.1 * y.1 + x.2 * y.2) := by
  intro x y
  rw [hq]
  unfold opticalMetric2
  have hN2 : N^2 ≠ 0 := pow_ne_zero 2 hN
  have hinv : (N⁻²)⁻¹ = N^2 := by
    simp [inv_pow, hN]
  rw [hinv]

/-- Equivalently the inverse form is
`N_opt⁻²(-dT²+dR²)`. -/
theorem opticalInverseMetric2_lapse_form
    (N q : ℝ)
    (hq : q = N⁻²) :
    ∀ x y : R2,
      opticalInverseMetric2 q x y =
        N⁻² * (-x.1 * y.1 + x.2 * y.2) := by
  intro x y
  rw [hq]
  rfl

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


/-! ### Covector-level synchronization and principal-orbit normalization -/

section SynchronizationCovector

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Forced synchronization correction between the exact radar clock differential and
the locally normalized chronometric covector. -/
def synchronizationCovector
    (dRadar TO : V →ₗ[ℝ] ℝ) :
    V →ₗ[ℝ] ℝ :=
  dRadar - TO

/-- By construction the exact radar covector is the local clock plus the unique correction. -/
theorem synchronizationCovector_decomposition
    (dRadar TO : V →ₗ[ℝ] ℝ) :
    dRadar = TO + synchronizationCovector dRadar TO := by
  ext v
  simp [synchronizationCovector]

/-- Any correction satisfying the same decomposition is the constructed one. -/
theorem synchronizationCovector_unique
    (dRadar TO β : V →ₗ[ℝ] ℝ)
    (hβ : dRadar = TO + β) :
    β = synchronizationCovector dRadar TO := by
  ext v
  have hv := LinearMap.congr_fun hβ v
  change dRadar v = TO v + β v at hv
  simp [synchronizationCovector]
  linarith

/-- If radar and local clocks both advance at unit rate on the selected clock direction,
the synchronization correction vanishes there. -/
theorem synchronizationCovector_vanishes_on_clock
    (dRadar TO : V →ₗ[ℝ] ℝ)
    (u : V)
    (hRadar : dRadar u = 1)
    (hTO : TO u = 1) :
    synchronizationCovector dRadar TO u = 0 := by
  simp [synchronizationCovector, hRadar, hTO]

/-- Principal specialization of the manuscript condition `β^{pr}|_γ=0`. -/
theorem principalSynchronization_vanishes
    (dRadar : (Fin 4 → ℝ) →ₗ[ℝ] ℝ)
    (hRadar : dRadar principalUhat = 1) :
    synchronizationCovector dRadar principalTOLinear
      principalUhat = 0 := by
  exact synchronizationCovector_vanishes_on_clock
    dRadar principalTOLinear principalUhat
    hRadar (by simpa [principalTOLinear_apply] using principalTO_unit)

end SynchronizationCovector

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


/-- The Liouville primitive annihilates the Euler/common-scale direction itself. -/
@[simp] theorem clockLiouville_horizontal_Euler (κ : ℝ) :
    clockLiouville κ (clockEuler κ) = 0 := by
  simp [clockLiouville, clockEuler]


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


/-- Full pullback homogeneity under positive/common-scale dilation, including the tangent map. -/
theorem clockLiouville_dilation_pullback
    (c κ : ℝ) (v : R2) :
    clockLiouville (c * κ)
      (clockDilationTangent c v) =
      c * clockLiouville κ v := by
  rcases v with ⟨vΘ, vκ⟩
  simp [clockLiouville, clockDilationTangent]
  ring


/-- Every tangent vector at positive scale is the dilation of a unique explicit vector
at the unit-scale section. -/
def clockUndilateTangent (κ : ℝ) (v : R2) : R2 :=
  (v.1, v.2 / κ)

theorem clockDilation_undilate
    (κ : ℝ) (hκ : κ ≠ 0) (v : R2) :
    clockDilationTangent κ (clockUndilateTangent κ v) = v := by
  rcases v with ⟨vΘ, vκ⟩
  ext <;>
    simp [clockDilationTangent, clockUndilateTangent, hκ]

/-- One-homogeneity and the already-normalized unit section force the clock-cover
one-form uniquely to be `κ dΘ`; there is no residual homogeneous choice. -/
theorem clockLiouville_unique_of_homogeneity
    (vartheta : ℝ → R2 → ℝ)
    (hhom :
      ∀ c κ : ℝ, ∀ v : R2,
        0 < c →
        vartheta (c * κ) (clockDilationTangent c v) =
          c * vartheta κ v)
    (hunit :
      ∀ v : R2, vartheta 1 v = clockDTheta v)
    (κ : ℝ) (hκ : 0 < κ) (v : R2) :
    vartheta κ v = clockLiouville κ v := by
  let v0 := clockUndilateTangent κ v
  have hdil :
      clockDilationTangent κ v0 = v :=
    clockDilation_undilate κ (ne_of_gt hκ) v
  have hh := hhom κ 1 v0 hκ
  rw [mul_one, hdil, hunit] at hh
  rw [hh]
  rcases v with ⟨vΘ, vκ⟩
  simp [v0, clockUndilateTangent, clockDTheta, clockLiouville]

/-- Therefore any two one-homogeneous clock-cover one-forms agreeing with the normalized
clock on `κ=1` coincide throughout the positive cover. -/
theorem clockCoverOneForm_unique
    (vartheta₁ vartheta₂ : ℝ → R2 → ℝ)
    (hhom₁ :
      ∀ c κ : ℝ, ∀ v : R2,
        0 < c →
        vartheta₁ (c * κ) (clockDilationTangent c v) =
          c * vartheta₁ κ v)
    (hhom₂ :
      ∀ c κ : ℝ, ∀ v : R2,
        0 < c →
        vartheta₂ (c * κ) (clockDilationTangent c v) =
          c * vartheta₂ κ v)
    (hunit₁ :
      ∀ v : R2, vartheta₁ 1 v = clockDTheta v)
    (hunit₂ :
      ∀ v : R2, vartheta₂ 1 v = clockDTheta v)
    (κ : ℝ) (hκ : 0 < κ) (v : R2) :
    vartheta₁ κ v = vartheta₂ κ v := by
  rw [clockLiouville_unique_of_homogeneity
        vartheta₁ hhom₁ hunit₁ κ hκ v,
      clockLiouville_unique_of_homogeneity
        vartheta₂ hhom₂ hunit₂ κ hκ v]

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
  have hparam : θ - (T x + t) + t = θ - T x := by ring
  rw [hparam]

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
  have hparam : θ - (T x + t) + t = θ - T x := by ring
  rw [hparam]

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

/-- Polar derivative of the Kerr-Newman separability scalar. -/
theorem Sigma_hasDerivAt_theta (r a θ : ℝ) :
    HasDerivAt (fun x : ℝ => Sigma r a x)
      (-2 * a^2 * Real.cos θ * Real.sin θ) θ := by
  have hc := (Real.hasDerivAt_cos θ).pow 2
  have hs := hc.const_mul (a^2)
  have hsum := hs.const_add (r^2)
  unfold Sigma
  convert hsum using 1 <;> ring

/-- Boyer-Lindquist time component of the Kerr-Newman potential
`A=-(Qr/Σ)(dt-a sin²θ dφ)`. -/
def kerrPotentialT (Q r a θ : ℝ) : ℝ :=
  -Q * r / Sigma r a θ

/-- Boyer-Lindquist azimuthal component of the same potential. -/
def kerrPotentialPhi (Q r a θ : ℝ) : ℝ :=
  Q * r * a * (Real.sin θ)^2 / Sigma r a θ

/-- Principal-frame electric component of the Kerr-Newman Maxwell field. -/
def kerrPrincipalE (Q r a θ : ℝ) : ℝ :=
  Q * (r^2 - a^2 * (Real.cos θ)^2) / (Sigma r a θ)^2

/-- Principal-frame magnetic component of the Kerr-Newman Maxwell field. -/
def kerrPrincipalB (Q r a θ : ℝ) : ℝ :=
  2 * Q * a * r * Real.cos θ / (Sigma r a θ)^2


/-! ### Differential Maxwell equations for the explicit Kerr-Newman field -/

/-- Radial derivative of the principal electric field. -/
theorem kerrPrincipalE_hasDerivAt_r
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrPrincipalE Q x a θ)
      (-2 * Q * r *
        (r^2 - 3 * a^2 * (Real.cos θ)^2) /
        (Sigma r a θ)^3) r := by
  have hn0 :
      HasDerivAt
        (fun x : ℝ => x^2 - a^2 * (Real.cos θ)^2)
        (2 * r) r := by
    convert ((hasDerivAt_id r).pow 2).sub_const
      (a^2 * (Real.cos θ)^2) using 1 <;> ring
  have hn := hn0.const_mul Q
  have hd := (Sigma_hasDerivAt_r r a θ).pow 2
  have hraw := hn.fun_div hd (pow_ne_zero 2 hsig)
  unfold kerrPrincipalE
  convert hraw using 1
  field_simp [hsig]
  unfold Sigma
  ring

/-- Polar derivative of the principal electric field. -/
theorem kerrPrincipalE_hasDerivAt_theta
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrPrincipalE Q r a x)
      (2 * Q * a^2 *
        (3 * r^2 - a^2 * (Real.cos θ)^2) *
        Real.sin θ * Real.cos θ /
        (Sigma r a θ)^3) θ := by
  have hc2 := (Real.hasDerivAt_cos θ).pow 2
  have hneg :
      HasDerivAt
        (fun x : ℝ => -(a^2) * (Real.cos x)^2)
        (2 * a^2 * Real.cos θ * Real.sin θ) θ := by
    convert hc2.const_mul (-(a^2)) using 1 <;> ring
  have hn0 :
      HasDerivAt
        (fun x : ℝ => r^2 - a^2 * (Real.cos x)^2)
        (2 * a^2 * Real.cos θ * Real.sin θ) θ := by
    simpa [sub_eq_add_neg, mul_assoc] using hneg.const_add (r^2)
  have hn := hn0.const_mul Q
  have hd := (Sigma_hasDerivAt_theta r a θ).pow 2
  have hraw := hn.fun_div hd (pow_ne_zero 2 hsig)
  unfold kerrPrincipalE
  convert hraw using 1
  field_simp [hsig]
  unfold Sigma
  ring

/-- Radial derivative of the principal magnetic field. -/
theorem kerrPrincipalB_hasDerivAt_r
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrPrincipalB Q x a θ)
      (-2 * Q * a *
        (3 * r^2 - a^2 * (Real.cos θ)^2) *
        Real.cos θ /
        (Sigma r a θ)^3) r := by
  have hn :
      HasDerivAt
        (fun x : ℝ =>
          (2 * Q * a * Real.cos θ) * x)
        (2 * Q * a * Real.cos θ) r :=
    (hasDerivAt_id r).const_mul
      (2 * Q * a * Real.cos θ)
  have hd := (Sigma_hasDerivAt_r r a θ).pow 2
  have hraw := hn.fun_div hd (pow_ne_zero 2 hsig)
  unfold kerrPrincipalB
  convert hraw using 1
  field_simp [hsig]
  unfold Sigma
  ring

/-- Polar derivative of the principal magnetic field. -/
theorem kerrPrincipalB_hasDerivAt_theta
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrPrincipalB Q r a x)
      (-2 * Q * a * r *
        (r^2 - 3 * a^2 * (Real.cos θ)^2) *
        Real.sin θ /
        (Sigma r a θ)^3) θ := by
  have hn :=
    (Real.hasDerivAt_cos θ).const_mul
      (2 * Q * a * r)
  have hd := (Sigma_hasDerivAt_theta r a θ).pow 2
  have hraw := hn.fun_div hd (pow_ne_zero 2 hsig)
  unfold kerrPrincipalB
  convert hraw using 1
  field_simp [hsig]
  unfold Sigma
  ring

/-- Densitized raised radial-time component
`sqrt(-g) F^{rt}=-(r²+a²) sinθ E`. -/
def kerrDensitizedFrt (Q r a θ : ℝ) : ℝ :=
  -(r^2 + a^2) * Real.sin θ *
    kerrPrincipalE Q r a θ

/-- Densitized raised polar-time component
`sqrt(-g) F^{θt}=a sin²θ B`. -/
def kerrDensitizedFthetaT (Q r a θ : ℝ) : ℝ :=
  a * (Real.sin θ)^2 * kerrPrincipalB Q r a θ

/-- Densitized raised radial-azimuthal component
`sqrt(-g) F^{rφ}=-a sinθ E`. -/
def kerrDensitizedFrPhi (Q r a θ : ℝ) : ℝ :=
  -a * Real.sin θ * kerrPrincipalE Q r a θ

/-- Densitized raised polar-azimuthal component
`sqrt(-g) F^{θφ}=B`. -/
def kerrDensitizedFthetaPhi (Q r a θ : ℝ) : ℝ :=
  kerrPrincipalB Q r a θ

/-- Radial derivative of the densitized time flux. -/
theorem kerrDensitizedFrt_hasDerivAt_r
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrDensitizedFrt Q x a θ)
      ((-2 * r * Real.sin θ) *
          kerrPrincipalE Q r a θ +
        (-(r^2 + a^2) * Real.sin θ) *
          (-2 * Q * r *
            (r^2 - 3 * a^2 * (Real.cos θ)^2) /
            (Sigma r a θ)^3)) r := by
  have hc0 :
      HasDerivAt
        (fun x : ℝ => -(x^2 + a^2) * Real.sin θ)
        (-2 * r * Real.sin θ) r := by
    have hsq := (hasDerivAt_id r).pow 2
    have hadd := hsq.add_const (a^2)
    convert hadd.neg.mul_const (Real.sin θ) using 1 <;> ring
  have hE := kerrPrincipalE_hasDerivAt_r Q r a θ hsig
  simpa [kerrDensitizedFrt] using hc0.mul hE

/-- Polar derivative of the densitized time flux. -/
theorem kerrDensitizedFthetaT_hasDerivAt_theta
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrDensitizedFthetaT Q r a x)
      ((2 * a * Real.sin θ * Real.cos θ) *
          kerrPrincipalB Q r a θ +
        (a * (Real.sin θ)^2) *
          (-2 * Q * a * r *
            (r^2 - 3 * a^2 * (Real.cos θ)^2) *
            Real.sin θ /
            (Sigma r a θ)^3)) θ := by
  have hs2 := (Real.hasDerivAt_sin θ).pow 2
  have hc :
      HasDerivAt
        (fun x : ℝ => a * (Real.sin x)^2)
        (2 * a * Real.sin θ * Real.cos θ) θ := by
    convert hs2.const_mul a using 1 <;> ring
  have hB := kerrPrincipalB_hasDerivAt_theta Q r a θ hsig
  simpa [kerrDensitizedFthetaT] using hc.mul hB

/-- First nontrivial source-free Maxwell equation in Boyer-Lindquist coordinates. -/
theorem kerrMaxwell_divergence_t
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    deriv (fun x : ℝ => kerrDensitizedFrt Q x a θ) r +
      deriv (fun x : ℝ => kerrDensitizedFthetaT Q r a x) θ = 0 := by
  rw [(kerrDensitizedFrt_hasDerivAt_r Q r a θ hsig).deriv,
      (kerrDensitizedFthetaT_hasDerivAt_theta
        Q r a θ hsig).deriv]
  unfold kerrPrincipalE kerrPrincipalB
  have htrig :
      (Real.sin θ)^2 = 1 - (Real.cos θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [htrig]
  field_simp [hsig]
  unfold Sigma
  ring

/-- Second nontrivial source-free Maxwell equation in Boyer-Lindquist coordinates. -/
theorem kerrMaxwell_divergence_phi
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    deriv (fun x : ℝ => kerrDensitizedFrPhi Q x a θ) r +
      deriv (fun x : ℝ => kerrDensitizedFthetaPhi Q r a x) θ = 0 := by
  have hr :
      HasDerivAt
        (fun x : ℝ => kerrDensitizedFrPhi Q x a θ)
        ((-a * Real.sin θ) *
          (-2 * Q * r *
            (r^2 - 3 * a^2 * (Real.cos θ)^2) /
            (Sigma r a θ)^3)) r := by
    simpa [kerrDensitizedFrPhi] using
      (kerrPrincipalE_hasDerivAt_r Q r a θ hsig).const_mul
        (-a * Real.sin θ)
  have hth :=
    kerrPrincipalB_hasDerivAt_theta Q r a θ hsig
  rw [hr.deriv, hth.deriv]
  unfold kerrPrincipalE kerrPrincipalB
  field_simp [hsig]
  unfold Sigma
  ring


/-- Homogeneous Maxwell/Bianchi equation in the `(r,θ,t)` sector:
`∂_r F_{θt}-∂_θ F_{rt}=0`. -/
theorem kerrMaxwell_bianchi_t
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    deriv
        (fun x : ℝ =>
          -a * Real.sin θ * kerrPrincipalB Q x a θ) r -
      deriv
        (fun x : ℝ =>
          kerrPrincipalE Q r a x) θ = 0 := by
  have hr :=
    (kerrPrincipalB_hasDerivAt_r Q r a θ hsig).const_mul
      (-a * Real.sin θ)
  have hth :=
    kerrPrincipalE_hasDerivAt_theta Q r a θ hsig
  rw [hr.deriv, hth.deriv]
  field_simp [hsig]
  unfold Sigma
  ring

/-- Homogeneous Maxwell/Bianchi equation in the `(r,θ,φ)` sector:
`∂_r F_{θφ}-∂_θ F_{rφ}=0`. -/
theorem kerrMaxwell_bianchi_phi
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    deriv
        (fun x : ℝ =>
          (x^2 + a^2) * Real.sin θ *
            kerrPrincipalB Q x a θ) r -
      deriv
        (fun x : ℝ =>
          -a * (Real.sin x)^2 *
            kerrPrincipalE Q r a x) θ = 0 := by
  have hcR :
      HasDerivAt
        (fun x : ℝ => (x^2 + a^2) * Real.sin θ)
        (2 * r * Real.sin θ) r := by
    convert (((hasDerivAt_id r).pow 2).add_const (a^2)).mul_const
      (Real.sin θ) using 1 <;> ring
  have hBr :=
    kerrPrincipalB_hasDerivAt_r Q r a θ hsig
  have hr := hcR.mul hBr

  have hs2 := (Real.hasDerivAt_sin θ).pow 2
  have hcθ :
      HasDerivAt
        (fun x : ℝ => -a * (Real.sin x)^2)
        (-2 * a * Real.sin θ * Real.cos θ) θ := by
    convert hs2.const_mul (-a) using 1 <;> ring
  have hEθ :=
    kerrPrincipalE_hasDerivAt_theta Q r a θ hsig
  have hth := hcθ.mul hEθ

  rw [hr.deriv, hth.deriv]
  unfold kerrPrincipalE kerrPrincipalB
  have htrig :
      (Real.sin θ)^2 = 1 - (Real.cos θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [htrig]
  field_simp [hsig]
  unfold Sigma
  ring

/-- The stationary-axisymmetric potential-derived field therefore satisfies the full
Maxwell system in the regular chart: both nontrivial Bianchi identities and both
nontrivial source-free divergence equations vanish. -/
theorem kerrMaxwell_equations_scalar_certificate
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    deriv
        (fun x : ℝ =>
          -a * Real.sin θ * kerrPrincipalB Q x a θ) r -
      deriv
        (fun x : ℝ =>
          kerrPrincipalE Q r a x) θ = 0 ∧
    deriv
        (fun x : ℝ =>
          (x^2 + a^2) * Real.sin θ *
            kerrPrincipalB Q x a θ) r -
      deriv
        (fun x : ℝ =>
          -a * (Real.sin x)^2 *
            kerrPrincipalE Q r a x) θ = 0 ∧
    deriv (fun x : ℝ => kerrDensitizedFrt Q x a θ) r +
      deriv (fun x : ℝ => kerrDensitizedFthetaT Q r a x) θ = 0 ∧
    deriv (fun x : ℝ => kerrDensitizedFrPhi Q x a θ) r +
      deriv (fun x : ℝ => kerrDensitizedFthetaPhi Q r a x) θ = 0 := by
  exact ⟨kerrMaxwell_bianchi_t Q r a θ hsig,
    kerrMaxwell_bianchi_phi Q r a θ hsig,
    kerrMaxwell_divergence_t Q r a θ hsig,
    kerrMaxwell_divergence_phi Q r a θ hsig⟩


/-- The radial derivative of `A_t` is exactly the principal electric coefficient. -/
theorem kerrPotentialT_hasDerivAt_r
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt (fun x : ℝ => kerrPotentialT Q x a θ)
      (kerrPrincipalE Q r a θ) r := by
  have hn : HasDerivAt (fun x : ℝ => -Q * x) (-Q) r :=
    (hasDerivAt_id r).const_mul (-Q)
  have hd := Sigma_hasDerivAt_r r a θ
  have hraw := hn.fun_div hd hsig
  unfold kerrPotentialT
  convert hraw using 1
  unfold kerrPrincipalE Sigma
  field_simp [hsig]
  ring

/-- The radial derivative of `A_φ` is the same electric coefficient with the forced
Boyer-Lindquist factor `-a sin²θ`. -/
theorem kerrPotentialPhi_hasDerivAt_r
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt (fun x : ℝ => kerrPotentialPhi Q x a θ)
      (-a * (Real.sin θ)^2 * kerrPrincipalE Q r a θ) r := by
  have hQ : HasDerivAt (fun x : ℝ => Q * x) Q r :=
    (hasDerivAt_id r).const_mul Q
  have hQa :
      HasDerivAt (fun x : ℝ => Q * x * a) (Q * a) r := by
    simpa using hQ.mul_const a
  have hn :
      HasDerivAt
        (fun x : ℝ => Q * x * a * (Real.sin θ)^2)
        (Q * a * (Real.sin θ)^2) r := by
    simpa [mul_assoc] using hQa.mul_const ((Real.sin θ)^2)
  have hd := Sigma_hasDerivAt_r r a θ
  have hraw := hn.fun_div hd hsig
  unfold kerrPotentialPhi
  convert hraw using 1
  unfold kerrPrincipalE Sigma
  field_simp [hsig]
  ring

/-- The polar derivative of `A_t` is the principal magnetic coefficient with factor
`-a sinθ`. -/
theorem kerrPotentialT_hasDerivAt_theta
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt (fun x : ℝ => kerrPotentialT Q r a x)
      (-a * Real.sin θ * kerrPrincipalB Q r a θ) θ := by
  have hn : HasDerivAt (fun _ : ℝ => -Q * r) 0 θ :=
    hasDerivAt_const θ (-Q * r)
  have hd := Sigma_hasDerivAt_theta r a θ
  have hraw := hn.fun_div hd hsig
  unfold kerrPotentialT
  convert hraw using 1
  unfold kerrPrincipalB Sigma
  field_simp [hsig]
  ring

/-- The polar derivative of `A_φ` carries the complementary principal factor
`(r²+a²) sinθ`. -/
theorem kerrPotentialPhi_hasDerivAt_theta
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt (fun x : ℝ => kerrPotentialPhi Q r a x)
      ((r^2 + a^2) * Real.sin θ * kerrPrincipalB Q r a θ) θ := by
  have hsin2 := (Real.hasDerivAt_sin θ).pow 2
  have hn :
      HasDerivAt
        (fun x : ℝ => (Q * r * a) * (Real.sin x)^2)
        ((Q * r * a) * (2 * Real.sin θ * Real.cos θ)) θ := by
    convert hsin2.const_mul (Q * r * a) using 1 <;> ring
  have hd := Sigma_hasDerivAt_theta r a θ
  have hraw := hn.fun_div hd hsig
  unfold kerrPotentialPhi
  convert hraw using 1
  unfold kerrPrincipalB Sigma
  field_simp [hsig]
  ring

/-- The four nonzero coordinate derivatives of the Kerr-Newman potential therefore
factor through the two principal field scalars `E` and `B`. -/
theorem kerrPotential_field_factorization
    (Q r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt (fun x : ℝ => kerrPotentialT Q x a θ)
        (kerrPrincipalE Q r a θ) r ∧
    HasDerivAt (fun x : ℝ => kerrPotentialPhi Q x a θ)
        (-a * (Real.sin θ)^2 * kerrPrincipalE Q r a θ) r ∧
    HasDerivAt (fun x : ℝ => kerrPotentialT Q r a x)
        (-a * Real.sin θ * kerrPrincipalB Q r a θ) θ ∧
    HasDerivAt (fun x : ℝ => kerrPotentialPhi Q r a x)
        ((r^2 + a^2) * Real.sin θ * kerrPrincipalB Q r a θ) θ := by
  exact ⟨kerrPotentialT_hasDerivAt_r Q r a θ hsig,
    kerrPotentialPhi_hasDerivAt_r Q r a θ hsig,
    kerrPotentialT_hasDerivAt_theta Q r a θ hsig,
    kerrPotentialPhi_hasDerivAt_theta Q r a θ hsig⟩


/-- Stationary one-form coefficients of the first Kerr-Newman metric square
`dt-a sin²θ dφ`. -/
def kerrTemporalOneFormCoeffs (a θ : ℝ) : R2 :=
  (1, -a * (Real.sin θ)^2)

/-- Stationary one-form coefficients of the second metric square
`a dt-(r²+a²)dφ`. -/
def kerrAxialOneFormCoeffs (r a : ℝ) : R2 :=
  (a, -(r^2 + a^2))

/-- Radial coordinate block of `F=dA`, represented by its `(dt,dφ)` coefficients. -/
def kerrRadialFieldBlock (Q r a θ : ℝ) : R2 :=
  (kerrPrincipalE Q r a θ,
    -a * (Real.sin θ)^2 * kerrPrincipalE Q r a θ)

/-- Polar coordinate block of `F=dA`. -/
def kerrPolarFieldBlock (Q r a θ : ℝ) : R2 :=
  (-a * Real.sin θ * kerrPrincipalB Q r a θ,
    (r^2 + a^2) * Real.sin θ * kerrPrincipalB Q r a θ)

/-- The radial Maxwell block lies exactly on the first Carter metric-square one-form. -/
theorem kerrRadialFieldBlock_carter_aligned
    (Q r a θ : ℝ) :
    kerrRadialFieldBlock Q r a θ =
      (kerrPrincipalE Q r a θ) •
        kerrTemporalOneFormCoeffs a θ := by
  ext <;>
    simp [kerrRadialFieldBlock, kerrTemporalOneFormCoeffs] <;>
    ring

/-- The polar Maxwell block lies exactly on the second Carter metric-square one-form,
with the orientation factor `-B sinθ`. -/
theorem kerrPolarFieldBlock_carter_aligned
    (Q r a θ : ℝ) :
    kerrPolarFieldBlock Q r a θ =
      (-kerrPrincipalB Q r a θ * Real.sin θ) •
        kerrAxialOneFormCoeffs r a := by
  ext <;>
    simp [kerrPolarFieldBlock, kerrAxialOneFormCoeffs] <;>
    ring

/-- Thus the potential-derived electromagnetic field and the square-form metric select
the same two stationary principal one-form directions. -/
theorem kerrPotential_metric_principal_alignment
    (Q r a θ : ℝ) :
    kerrRadialFieldBlock Q r a θ =
        (kerrPrincipalE Q r a θ) •
          kerrTemporalOneFormCoeffs a θ ∧
    kerrPolarFieldBlock Q r a θ =
        (-kerrPrincipalB Q r a θ * Real.sin θ) •
          kerrAxialOneFormCoeffs r a :=
  ⟨kerrRadialFieldBlock_carter_aligned Q r a θ,
    kerrPolarFieldBlock_carter_aligned Q r a θ⟩

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


/-- First finite radial carrier jet that actually resolves the residual boost. -/
def kerrResolvingQMinus (r a θ : ℝ) : ℝ :=
  if r = 0 then -4 / Sigma 0 a θ
  else kerrRadialGradient r a θ

def kerrResolvingQPlus (r a θ : ℝ) : ℝ :=
  - kerrResolvingQMinus r a θ

/-- The resolving component is nonzero at every regular Kerr-Newman point. -/
theorem kerrResolvingQMinus_ne_zero
    (r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    kerrResolvingQMinus r a θ ≠ 0 := by
  by_cases hr : r = 0
  · subst r
    simp [kerrResolvingQMinus,
      kerrRadialGradient_second_at_zero_ne a θ hsig]
  · simp [kerrResolvingQMinus, hr,
      (kerrRadialLogGradient_ne_zero_iff r a θ hsig).2 hr]

/-- The first finite resolving jet always has equal-and-opposite null components. -/
theorem kerrResolvingQPlus_eq_neg (r a θ : ℝ) :
    kerrResolvingQPlus r a θ =
      - kerrResolvingQMinus r a θ := rfl

/-- Hence the unique carrier-selected residual boost is zero on the entire regular stratum,
including the `r=0` points resolved by the second jet. -/
theorem kerrResolving_balance_rapidity_zero
    (r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    sigmaStar
      (kerrResolvingQMinus r a θ)
      (kerrResolvingQPlus r a θ) = 0 := by
  rw [kerrResolvingQPlus_eq_neg]
  exact sigmaStar_opposite_components
    (kerrResolvingQMinus r a θ)
    (kerrResolvingQMinus_ne_zero r a θ hsig)

/-- The corresponding balanced optical observer is therefore the unboosted principal one
at every regular point. -/
theorem kerrResolving_balanced_observer_unboosted
    (r a θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    opticalObserver
      (sigmaStar
        (kerrResolvingQMinus r a θ)
        (kerrResolvingQPlus r a θ)) = TO := by
  rw [kerrResolving_balance_rapidity_zero r a θ hsig]
  ext <;> norm_num [opticalObserver, TO]

/-- Kerr-Newman `Δ`. -/
def Delta (r M a Q : ℝ) : ℝ := r^2 - 2*M*r + a^2 + Q^2

/-! ### Boyer-Lindquist metric inverse and densitized Maxwell field -/

/-- Covariant stationary metric coefficients obtained by expanding the two square-form
stationary one-forms. -/
def kerrGtt (r M a Q θ : ℝ) : ℝ :=
  (-Delta r M a Q + a^2 * (Real.sin θ)^2) /
    Sigma r a θ

def kerrGtPhi (r M a Q θ : ℝ) : ℝ :=
  a * (Real.sin θ)^2 *
    (Delta r M a Q - (r^2 + a^2)) /
    Sigma r a θ

def kerrGPhiPhi (r M a Q θ : ℝ) : ℝ :=
  (Real.sin θ)^2 *
    ((r^2 + a^2)^2 -
      a^2 * Delta r M a Q * (Real.sin θ)^2) /
    Sigma r a θ

def kerrGrr (r M a Q θ : ℝ) : ℝ :=
  Sigma r a θ / Delta r M a Q

def kerrGthetaTheta (r a θ : ℝ) : ℝ :=
  Sigma r a θ

/-- The stationary square-form metric makes g_phiphi algebraically dependent on g_tphi
plus the flat oblate angular factor. -/
theorem kerrGPhiPhi_from_tphi
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    kerrGPhiPhi r M a Q θ =
      -a * (Real.sin θ)^2 * kerrGtPhi r M a Q θ +
        (Real.sin θ)^2 * (r^2 + a^2) := by
  unfold kerrGPhiPhi kerrGtPhi
  field_simp [hsig]
  ring

/-- Compact Kerr-Newman mass/charge factor `H=2Mr-Q²`. -/
def kerrH (r M Q : ℝ) : ℝ :=
  2 * M * r - Q^2


/-- Radial derivative of Kerr-Newman `Δ`. -/
theorem Delta_hasDerivAt_r (r M a Q : ℝ) :
    HasDerivAt (fun x : ℝ => Delta x M a Q)
      (2 * (r - M)) r := by
  unfold Delta
  convert (((hasDerivAt_id r).pow 2).sub
    ((hasDerivAt_id r).const_mul (2 * M))).add_const
      (a^2 + Q^2) using 1 <;> ring

/-- Simplified stationary metric coefficients on the regular `Σ ≠ 0` chart. -/
theorem kerrGtt_alt
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    kerrGtt r M a Q θ =
      -1 + kerrH r M Q / Sigma r a θ := by
  unfold kerrGtt kerrH Delta
  field_simp [hsig]
  unfold Sigma
  ring

theorem kerrGtPhi_alt
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    kerrGtPhi r M a Q θ =
      -a * (Real.sin θ)^2 *
        kerrH r M Q / Sigma r a θ := by
  unfold kerrGtPhi kerrH Delta
  field_simp [hsig]
  ring

theorem kerrGPhiPhi_alt
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    kerrGPhiPhi r M a Q θ =
      (Real.sin θ)^2 * (r^2 + a^2) +
      a^2 * (Real.sin θ)^4 *
        kerrH r M Q / Sigma r a θ := by
  unfold kerrGPhiPhi kerrH Delta
  field_simp [hsig]
  have htrig :
      (Real.sin θ)^2 + (Real.cos θ)^2 = 1 :=
    Real.sin_sq_add_cos_sq θ
  unfold Sigma
  nlinarith

/-- Radial derivative of `H`. -/
theorem kerrH_hasDerivAt_r (r M Q : ℝ) :
    HasDerivAt (fun x : ℝ => kerrH x M Q) (2 * M) r := by
  have hlin :=
    (hasDerivAt_id r).const_mul (2 * M)
  have hsub := hlin.sub_const (Q^2)
  unfold kerrH
  convert hsub using 1 <;> ring

/-- Radial derivative of `g_tt`. -/
theorem kerrGtt_hasDerivAt_r
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrGtt x M a Q θ)
      (2 * (M * (a^2 * (Real.cos θ)^2 - r^2) + Q^2 * r) /
        (Sigma r a θ)^2) r := by
  have hn :
      HasDerivAt
        (fun x : ℝ =>
          -Delta x M a Q + a^2 * (Real.sin θ)^2)
        (-2 * (r - M)) r := by
    convert (Delta_hasDerivAt_r r M a Q).neg.add_const
      (a^2 * (Real.sin θ)^2) using 1 <;> ring
  have hraw :=
    hn.fun_div (Sigma_hasDerivAt_r r a θ) hsig
  unfold kerrGtt
  convert hraw using 1
  field_simp [hsig]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma
  nlinarith

/-- Polar derivative of `g_tt`. -/
theorem kerrGtt_hasDerivAt_theta
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrGtt r M a Q x)
      (2 * a^2 * kerrH r M Q *
        Real.sin θ * Real.cos θ /
        (Sigma r a θ)^2) θ := by
  have hn :
      HasDerivAt
        (fun x : ℝ =>
          -Delta r M a Q + a^2 * (Real.sin x)^2)
        (2 * a^2 * Real.sin θ * Real.cos θ) θ := by
    have hs := (Real.hasDerivAt_sin θ).pow 2
    have hmul := hs.const_mul (a^2)
    have hadd := hmul.const_add (-Delta r M a Q)
    convert hadd using 1 <;> ring
  have hraw :=
    hn.fun_div (Sigma_hasDerivAt_theta r a θ) hsig
  unfold kerrGtt
  convert hraw using 1
  field_simp [hsig]
  unfold kerrH Delta Sigma
  ring

/-- Radial derivative of `g_tφ`. -/
theorem kerrGtPhi_hasDerivAt_r
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrGtPhi x M a Q θ)
      (-a * (Real.sin θ)^2 *
        (2 * (M * (a^2 * (Real.cos θ)^2 - r^2) + Q^2 * r) /
          (Sigma r a θ)^2)) r := by
  have hdiff :
      HasDerivAt
        (fun x : ℝ =>
          Delta x M a Q - (x^2 + a^2))
        (-2 * M) r := by
    convert (Delta_hasDerivAt_r r M a Q).sub
      (((hasDerivAt_id r).pow 2).add_const (a^2)) using 1 <;> ring
  have hn :=
    hdiff.const_mul (a * (Real.sin θ)^2)
  have hraw :=
    hn.fun_div (Sigma_hasDerivAt_r r a θ) hsig
  unfold kerrGtPhi
  convert hraw using 1
  field_simp [hsig]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma
  nlinarith

/-- Polar derivative of `g_tφ`. -/
theorem kerrGtPhi_hasDerivAt_theta
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrGtPhi r M a Q x)
      (-2 * a * kerrH r M Q * (r^2 + a^2) *
        Real.sin θ * Real.cos θ /
        (Sigma r a θ)^2) θ := by
  have hc :
      HasDerivAt
        (fun x : ℝ => a * (Real.sin x)^2)
        (2 * a * Real.sin θ * Real.cos θ) θ := by
    have hs2 := (Real.hasDerivAt_sin θ).pow 2
    have hmul := hs2.const_mul a
    convert hmul using 1 <;> ring
  have hconst :
      HasDerivAt
        (fun _ : ℝ =>
          Delta r M a Q - (r^2 + a^2))
        0 θ :=
    hasDerivAt_const θ
      (Delta r M a Q - (r^2 + a^2))
  have hn := hc.mul hconst
  have hraw :=
    hn.fun_div (Sigma_hasDerivAt_theta r a θ) hsig
  unfold kerrGtPhi
  convert hraw using 1
  field_simp [hsig]
  unfold kerrH Delta Sigma
  ring

/-- Radial derivative of `g_rr`. -/
theorem kerrGrr_hasDerivAt_r
    (r M a Q θ : ℝ) (hdel : Delta r M a Q ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrGrr x M a Q θ)
      (2 * (r * Delta r M a Q -
        (r - M) * Sigma r a θ) /
        (Delta r M a Q)^2) r := by
  have hraw :=
    (Sigma_hasDerivAt_r r a θ).fun_div
      (Delta_hasDerivAt_r r M a Q) hdel
  unfold kerrGrr
  convert hraw using 1
  field_simp [hdel]
  ring

/-- Polar derivative of `g_rr`. -/
theorem kerrGrr_hasDerivAt_theta
    (r M a Q θ : ℝ) (hdel : Delta r M a Q ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrGrr r M a Q x)
      (-2 * a^2 * Real.cos θ * Real.sin θ /
        Delta r M a Q) θ := by
  have hd :
      HasDerivAt (fun _ : ℝ => Delta r M a Q) 0 θ :=
    hasDerivAt_const θ (Delta r M a Q)
  have hraw :=
    (Sigma_hasDerivAt_theta r a θ).fun_div hd hdel
  simpa [kerrGrr] using hraw

/-- Derivatives of `g_θθ=Σ`. -/
theorem kerrGthetaTheta_hasDerivAt_r
    (r a θ : ℝ) :
    HasDerivAt
      (fun x : ℝ => kerrGthetaTheta x a θ)
      (2 * r) r := by
  simpa [kerrGthetaTheta] using
    Sigma_hasDerivAt_r r a θ

theorem kerrGthetaTheta_hasDerivAt_theta
    (r a θ : ℝ) :
    HasDerivAt
      (fun x : ℝ => kerrGthetaTheta r a x)
      (-2 * a^2 * Real.cos θ * Real.sin θ) θ := by
  simpa [kerrGthetaTheta] using
    Sigma_hasDerivAt_theta r a θ

/-- Radial derivative of `g_φφ`. -/
theorem kerrGPhiPhi_hasDerivAt_r
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrGPhiPhi x M a Q θ)
      (2 * r * (Real.sin θ)^2 +
        a^2 * (Real.sin θ)^4 *
          (2 * (M * (a^2 * (Real.cos θ)^2 - r^2) + Q^2 * r) /
            (Sigma r a θ)^2)) r := by
  have hR :
      HasDerivAt
        (fun x : ℝ => x^2 + a^2)
        (2 * r) r := by
    convert ((hasDerivAt_id r).pow 2).add_const (a^2) using 1 <;> ring
  have hR2 := hR.pow 2
  have hdel := Delta_hasDerivAt_r r M a Q
  have hinner :
      HasDerivAt
        (fun x : ℝ =>
          (x^2 + a^2)^2 -
            a^2 * Delta x M a Q * (Real.sin θ)^2)
        (4 * r * (r^2 + a^2) -
          2 * a^2 * (r - M) * (Real.sin θ)^2) r := by
    have hterm :=
      hdel.const_mul (a^2 * (Real.sin θ)^2)
    convert hR2.sub hterm using 1 <;> ring
  have hn :=
    hinner.const_mul ((Real.sin θ)^2)
  have hraw :=
    hn.fun_div (Sigma_hasDerivAt_r r a θ) hsig
  unfold kerrGPhiPhi
  convert hraw using 1
  field_simp [hsig]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma
  nlinarith

/-- Polar derivative of `g_φφ`. -/
theorem kerrGPhiPhi_hasDerivAt_theta
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrGPhiPhi r M a Q x)
      (2 * Real.sin θ * Real.cos θ * (r^2 + a^2) +
       2 * a^2 * kerrH r M Q *
         (Real.sin θ)^3 * Real.cos θ / Sigma r a θ +
       2 * a^2 * kerrH r M Q * (r^2 + a^2) *
         (Real.sin θ)^3 * Real.cos θ /
         (Sigma r a θ)^2) θ := by
  have hs2 := (Real.hasDerivAt_sin θ).pow 2
  have hA :
      HasDerivAt
        (fun x : ℝ =>
          (r^2 + a^2)^2 -
            a^2 * Delta r M a Q * (Real.sin x)^2)
        (-2 * a^2 * Delta r M a Q *
          Real.sin θ * Real.cos θ) θ := by
    have ht :=
      hs2.const_mul (a^2 * Delta r M a Q)
    convert (hasDerivAt_const θ ((r^2 + a^2)^2)).sub ht using 1 <;> ring
  have hn := hs2.mul hA
  have hraw :=
    hn.fun_div (Sigma_hasDerivAt_theta r a θ) hsig
  unfold kerrGPhiPhi
  convert hraw using 1
  field_simp [hsig]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold kerrH Delta Sigma
  nlinarith

/-- Contravariant stationary block and radial/polar inverse coefficients. -/
def kerrInvGtt (r M a Q θ : ℝ) : ℝ :=
  -((r^2 + a^2)^2 -
      a^2 * Delta r M a Q * (Real.sin θ)^2) /
    (Sigma r a θ * Delta r M a Q)

def kerrInvGtPhi (r M a Q θ : ℝ) : ℝ :=
  a * (Delta r M a Q - (r^2 + a^2)) /
    (Sigma r a θ * Delta r M a Q)

def kerrInvGPhiPhi (r M a Q θ : ℝ) : ℝ :=
  (Delta r M a Q - a^2 * (Real.sin θ)^2) /
    (Sigma r a θ * Delta r M a Q *
      (Real.sin θ)^2)

def kerrInvGrr (r M a Q θ : ℝ) : ℝ :=
  Delta r M a Q / Sigma r a θ

def kerrInvGthetaTheta (r a θ : ℝ) : ℝ :=
  1 / Sigma r a θ

/-- The stationary covariant block has determinant `-Δ sin²θ`. -/
theorem kerr_stationary_block_det
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0) :
    kerrGtt r M a Q θ * kerrGPhiPhi r M a Q θ -
      (kerrGtPhi r M a Q θ)^2 =
      -Delta r M a Q * (Real.sin θ)^2 := by
  unfold kerrGtt kerrGPhiPhi kerrGtPhi
  have htrig :
      (Real.sin θ)^2 = 1 - (Real.cos θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [htrig]
  field_simp [hsig]
  unfold Sigma
  ring

/-- Multiplying by the radial and polar blocks gives the full metric determinant
`det g=-Σ² sin²θ`. -/
theorem kerr_metric_det
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    (kerrGtt r M a Q θ * kerrGPhiPhi r M a Q θ -
        (kerrGtPhi r M a Q θ)^2) *
      kerrGrr r M a Q θ *
      kerrGthetaTheta r a θ =
      -(Sigma r a θ)^2 * (Real.sin θ)^2 := by
  rw [kerr_stationary_block_det r M a Q θ hsig]
  unfold kerrGrr kerrGthetaTheta
  field_simp [hdel]
  ring

/-- The displayed contravariant stationary coefficients invert the covariant block. -/
theorem kerr_stationary_inverse_block
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrGtt r M a Q θ * kerrInvGtt r M a Q θ +
        kerrGtPhi r M a Q θ * kerrInvGtPhi r M a Q θ = 1 ∧
    kerrGtt r M a Q θ * kerrInvGtPhi r M a Q θ +
        kerrGtPhi r M a Q θ * kerrInvGPhiPhi r M a Q θ = 0 ∧
    kerrGtPhi r M a Q θ * kerrInvGtt r M a Q θ +
        kerrGPhiPhi r M a Q θ * kerrInvGtPhi r M a Q θ = 0 ∧
    kerrGtPhi r M a Q θ * kerrInvGtPhi r M a Q θ +
        kerrGPhiPhi r M a Q θ * kerrInvGPhiPhi r M a Q θ = 1 := by
  have htrig :
      (Real.sin θ)^2 = 1 - (Real.cos θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  constructor
  · unfold kerrGtt kerrInvGtt kerrGtPhi kerrInvGtPhi
    rw [htrig]
    field_simp [hsig, hdel]
    unfold Sigma
    ring
  · constructor
    · unfold kerrGtt kerrInvGtPhi kerrGtPhi kerrInvGPhiPhi
      rw [htrig]
      field_simp [hsig, hdel, hsin]
      unfold Sigma
      ring
    · constructor
      · unfold kerrGtPhi kerrInvGtt kerrGPhiPhi kerrInvGtPhi
        rw [htrig]
        field_simp [hsig, hdel]
        unfold Sigma
        ring
      · unfold kerrGtPhi kerrInvGtPhi kerrGPhiPhi kerrInvGPhiPhi
        rw [htrig]
        field_simp [hsig, hdel, hsin]
        unfold Sigma
        ring

/-- Full covariant Boyer-Lindquist metric component function. -/
def kerrMetricCov
    (r M a Q θ : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kerrGtt r M a Q θ
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
    kerrGtPhi r M a Q θ
  else if i = 1 ∧ j = 1 then kerrGrr r M a Q θ
  else if i = 2 ∧ j = 2 then kerrGthetaTheta r a θ
  else if i = 3 ∧ j = 3 then kerrGPhiPhi r M a Q θ
  else 0

/-- Full contravariant Boyer-Lindquist inverse-metric component function. -/
def kerrMetricInv
    (r M a Q θ : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kerrInvGtt r M a Q θ
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
    kerrInvGtPhi r M a Q θ
  else if i = 1 ∧ j = 1 then kerrInvGrr r M a Q θ
  else if i = 2 ∧ j = 2 then kerrInvGthetaTheta r a θ
  else if i = 3 ∧ j = 3 then kerrInvGPhiPhi r M a Q θ
  else 0

/-- Both component functions are symmetric. -/
theorem kerrMetricCov_symmetric
    (r M a Q θ : ℝ) (i j : Fin 4) :
    kerrMetricCov r M a Q θ i j =
      kerrMetricCov r M a Q θ j i := by
  fin_cases i <;> fin_cases j <;>
    simp [kerrMetricCov]

theorem kerrMetricInv_symmetric
    (r M a Q θ : ℝ) (i j : Fin 4) :
    kerrMetricInv r M a Q θ i j =
      kerrMetricInv r M a Q θ j i := by
  fin_cases i <;> fin_cases j <;>
    simp [kerrMetricInv]

/-- The displayed contravariant metric is the actual inverse of the square-form
Boyer-Lindquist metric in every component. -/
theorem kerrMetric_inverse_certificate
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0)
    (i j : Fin 4) :
    (∑ k : Fin 4,
      kerrMetricCov r M a Q θ i k *
        kerrMetricInv r M a Q θ k j) =
      (if i = j then 1 else 0) := by
  rcases kerr_stationary_inverse_block
    r M a Q θ hsig hdel hsin with
    ⟨h00, h03, h30, h33⟩
  fin_cases i <;> fin_cases j <;>
    simp [kerrMetricCov, kerrMetricInv,
      h00, h03, h30, h33,
      kerrGrr, kerrInvGrr,
      kerrGthetaTheta, kerrInvGthetaTheta] <;>
    field_simp [hsig, hdel] <;>
    ring

/-- Scalar determinant of the Boyer-Lindquist metric. -/
def kerrMetricDetScalar (r a θ : ℝ) : ℝ :=
  -(Sigma r a θ)^2 * (Real.sin θ)^2

/-- The block determinant calculation is exactly the named metric determinant. -/
theorem kerr_metric_det_eq_scalar
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    (kerrGtt r M a Q θ * kerrGPhiPhi r M a Q θ -
        (kerrGtPhi r M a Q θ)^2) *
      kerrGrr r M a Q θ *
      kerrGthetaTheta r a θ =
      kerrMetricDetScalar r a θ := by
  rw [kerr_metric_det r M a Q θ hsig hdel]
  rfl

/-- Positive-chart Boyer-Lindquist volume density `sqrt(-g)=Σ sinθ`. -/
def kerrVolumeDensity (r a θ : ℝ) : ℝ :=
  Sigma r a θ * Real.sin θ

/-- Its square is exactly minus the metric determinant. -/
theorem kerrVolumeDensity_sq
    (r a θ : ℝ) :
    (kerrVolumeDensity r a θ)^2 =
      - kerrMetricDetScalar r a θ := by
  unfold kerrVolumeDensity kerrMetricDetScalar
  ring

/-- On the regular positive angular chart, the named density is literally
`sqrt(-det g)`. -/
theorem kerrVolumeDensity_eq_sqrt_neg_det
    (r a θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hsin : 0 < Real.sin θ) :
    kerrVolumeDensity r a θ =
      Real.sqrt (-kerrMetricDetScalar r a θ) := by
  have hvol : 0 ≤ kerrVolumeDensity r a θ := by
    unfold kerrVolumeDensity
    positivity
  rw [← kerrVolumeDensity_sq,
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg hvol]

/-! ### Coordinate Levi-Civita and Ricci tensors from the certified metric -/

/-- Boyer-Lindquist coordinate derivative of a stationary/axisymmetric scalar.
Coordinates are ordered `(t,r,θ,φ)=(0,1,2,3)`; only `r` and `θ` derivatives survive. -/
def kerrCoordPartial
    (μ : Fin 4) (f : ℝ → ℝ → ℝ) (r θ : ℝ) : ℝ :=
  if μ = 1 then deriv (fun x : ℝ => f x θ) r
  else if μ = 2 then deriv (fun x : ℝ => f r x) θ
  else 0

@[simp] theorem kerrCoordPartial_time
    (f : ℝ → ℝ → ℝ) (r θ : ℝ) :
    kerrCoordPartial 0 f r θ = 0 := by
  simp [kerrCoordPartial]

@[simp] theorem kerrCoordPartial_phi
    (f : ℝ → ℝ → ℝ) (r θ : ℝ) :
    kerrCoordPartial 3 f r θ = 0 := by
  simp [kerrCoordPartial]

/-- Genuine coordinate derivative of the covariant Kerr-Newman metric. -/
def kerrMetricPartial
    (μ : Fin 4) (r M a Q θ : ℝ)
    (i j : Fin 4) : ℝ :=
  kerrCoordPartial μ
    (fun rr th => kerrMetricCov rr M a Q th i j) r θ

/-- Metric symmetry survives coordinate differentiation. -/
theorem kerrMetricPartial_symmetric
    (μ : Fin 4) (r M a Q θ : ℝ)
    (i j : Fin 4) :
    kerrMetricPartial μ r M a Q θ i j =
      kerrMetricPartial μ r M a Q θ j i := by
  unfold kerrMetricPartial kerrCoordPartial
  by_cases h1 : μ = 1
  · rw [if_pos h1]
    have hfun :
        (fun x : ℝ => kerrMetricCov x M a Q θ i j) =
          (fun x : ℝ => kerrMetricCov x M a Q θ j i) := by
      funext x
      exact kerrMetricCov_symmetric x M a Q θ i j
    rw [hfun]
  · rw [if_neg h1]
    by_cases h2 : μ = 2
    · rw [if_pos h2]
      have hfun :
          (fun x : ℝ => kerrMetricCov r M a Q x i j) =
            (fun x : ℝ => kerrMetricCov r M a Q x j i) := by
        funext x
        exact kerrMetricCov_symmetric r M a Q x i j
      rw [hfun]
    · rw [if_neg h2]

/-! ### Explicit first-coordinate derivatives of the Kerr-Newman metric -/

/-- Radial derivative matrix of the covariant metric. -/
def kerrMetricRadialDerivative
    (r M a Q θ : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then
    2 * (M * (a^2 * (Real.cos θ)^2 - r^2) + Q^2 * r) /
      (Sigma r a θ)^2
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
    -a * (Real.sin θ)^2 *
      (2 * (M * (a^2 * (Real.cos θ)^2 - r^2) + Q^2 * r) /
        (Sigma r a θ)^2)
  else if i = 1 ∧ j = 1 then
    2 * (r * Delta r M a Q -
      (r - M) * Sigma r a θ) /
      (Delta r M a Q)^2
  else if i = 2 ∧ j = 2 then
    2 * r
  else if i = 3 ∧ j = 3 then
    2 * r * (Real.sin θ)^2 +
      a^2 * (Real.sin θ)^4 *
        (2 * (M * (a^2 * (Real.cos θ)^2 - r^2) + Q^2 * r) /
          (Sigma r a θ)^2)
  else 0

/-- Polar derivative matrix of the covariant metric. -/
def kerrMetricPolarDerivative
    (r M a Q θ : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then
    2 * a^2 * kerrH r M Q *
      Real.sin θ * Real.cos θ /
      (Sigma r a θ)^2
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
    -2 * a * kerrH r M Q * (r^2 + a^2) *
      Real.sin θ * Real.cos θ /
      (Sigma r a θ)^2
  else if i = 1 ∧ j = 1 then
    -2 * a^2 * Real.cos θ * Real.sin θ /
      Delta r M a Q
  else if i = 2 ∧ j = 2 then
    -2 * a^2 * Real.cos θ * Real.sin θ
  else if i = 3 ∧ j = 3 then
    2 * Real.sin θ * Real.cos θ * (r^2 + a^2) +
      2 * a^2 * kerrH r M Q *
        (Real.sin θ)^3 * Real.cos θ / Sigma r a θ +
      2 * a^2 * kerrH r M Q * (r^2 + a^2) *
        (Real.sin θ)^3 * Real.cos θ /
        (Sigma r a θ)^2
  else 0

/-- The actual radial metric partial is exactly the explicit radial derivative matrix. -/
theorem kerrMetricPartial_r
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (i j : Fin 4) :
    kerrMetricPartial 1 r M a Q θ i j =
      kerrMetricRadialDerivative r M a Q θ i j := by
  fin_cases i <;> fin_cases j <;>
    simp [kerrMetricPartial, kerrCoordPartial,
      kerrMetricCov, kerrMetricRadialDerivative,
      (kerrGtt_hasDerivAt_r r M a Q θ hsig).deriv,
      (kerrGtPhi_hasDerivAt_r r M a Q θ hsig).deriv,
      (kerrGrr_hasDerivAt_r r M a Q θ hdel).deriv,
      (kerrGthetaTheta_hasDerivAt_r r a θ).deriv,
      (kerrGPhiPhi_hasDerivAt_r r M a Q θ hsig).deriv]

/-- The actual polar metric partial is exactly the explicit polar derivative matrix. -/
theorem kerrMetricPartial_theta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (i j : Fin 4) :
    kerrMetricPartial 2 r M a Q θ i j =
      kerrMetricPolarDerivative r M a Q θ i j := by
  fin_cases i <;> fin_cases j <;>
    simp [kerrMetricPartial, kerrCoordPartial,
      kerrMetricCov, kerrMetricPolarDerivative,
      (kerrGtt_hasDerivAt_theta r M a Q θ hsig).deriv,
      (kerrGtPhi_hasDerivAt_theta r M a Q θ hsig).deriv,
      (kerrGrr_hasDerivAt_theta r M a Q θ hdel).deriv,
      (kerrGthetaTheta_hasDerivAt_theta r a θ).deriv,
      (kerrGPhiPhi_hasDerivAt_theta r M a Q θ hsig).deriv]

/-- Stationarity and axisymmetry kill the remaining coordinate metric derivatives. -/
@[simp] theorem kerrMetricPartial_t
    (r M a Q θ : ℝ) (i j : Fin 4) :
    kerrMetricPartial 0 r M a Q θ i j = 0 := by
  simp [kerrMetricPartial, kerrCoordPartial]

@[simp] theorem kerrMetricPartial_phi
    (r M a Q θ : ℝ) (i j : Fin 4) :
    kerrMetricPartial 3 r M a Q θ i j = 0 := by
  simp [kerrMetricPartial, kerrCoordPartial]

/-- Fully explicit coordinate derivative tensor on the regular stationary chart. -/
def kerrMetricDerivativeRegular
    (κ : Fin 4) (r M a Q θ : ℝ)
    (i j : Fin 4) : ℝ :=
  if κ = 1 then kerrMetricRadialDerivative r M a Q θ i j
  else if κ = 2 then kerrMetricPolarDerivative r M a Q θ i j
  else 0

/-- Every genuine coordinate derivative of the metric equals the explicit regular tensor. -/
theorem kerrMetricPartial_eq_regular
    (κ : Fin 4) (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (i j : Fin 4) :
    kerrMetricPartial κ r M a Q θ i j =
      kerrMetricDerivativeRegular κ r M a Q θ i j := by
  fin_cases κ
  · simp [kerrMetricDerivativeRegular]
  · simpa [kerrMetricDerivativeRegular] using
      kerrMetricPartial_r r M a Q θ hsig hdel i j
  · simpa [kerrMetricDerivativeRegular] using
      kerrMetricPartial_theta r M a Q θ hsig hdel i j
  · simp [kerrMetricDerivativeRegular]

/-- Algebraic Christoffel expression after all first coordinate derivatives have been evaluated. -/
def kerrChristoffelRegular
    (r M a Q θ : ℝ)
    (ρ μ ν : Fin 4) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ σ : Fin 4,
      kerrMetricInv r M a Q θ ρ σ *
        (kerrMetricDerivativeRegular μ r M a Q θ σ ν +
         kerrMetricDerivativeRegular ν r M a Q θ σ μ -
         kerrMetricDerivativeRegular σ r M a Q θ μ ν)

/-- Levi-Civita Christoffel symbols constructed directly from the metric and inverse metric. -/
def kerrChristoffel
    (r M a Q θ : ℝ)
    (ρ μ ν : Fin 4) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ σ : Fin 4,
      kerrMetricInv r M a Q θ ρ σ *
        (kerrMetricPartial μ r M a Q θ σ ν +
         kerrMetricPartial ν r M a Q θ σ μ -
         kerrMetricPartial σ r M a Q θ μ ν)

/-- On the regular chart, the genuine Levi-Civita Christoffels contain no remaining
unevaluated first derivatives. -/
theorem kerrChristoffel_eq_regular
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (ρ μ ν : Fin 4) :
    kerrChristoffel r M a Q θ ρ μ ν =
      kerrChristoffelRegular r M a Q θ ρ μ ν := by
  unfold kerrChristoffel kerrChristoffelRegular
  apply congrArg ((1 / 2 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [kerrMetricPartial_eq_regular μ r M a Q θ hsig hdel σ ν,
      kerrMetricPartial_eq_regular ν r M a Q θ hsig hdel σ μ,
      kerrMetricPartial_eq_regular σ r M a Q θ hsig hdel μ ν]


/-- The coordinate Levi-Civita connection is torsion-free by construction. -/
theorem kerrChristoffel_lower_symmetric
    (r M a Q θ : ℝ)
    (ρ μ ν : Fin 4) :
    kerrChristoffel r M a Q θ ρ μ ν =
      kerrChristoffel r M a Q θ ρ ν μ := by
  unfold kerrChristoffel
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [kerrMetricPartial_symmetric σ r M a Q θ μ ν]
  ring

/-! ### Stationary-reflection parity of the Levi-Civita connection -/

/-- Sign of a Boyer-Lindquist coordinate under `(t,φ) ↦ (-t,-φ)`. -/
def kerrStationarySign (i : Fin 4) : ℝ :=
  if i = 0 ∨ i = 3 then -1 else 1

@[simp] theorem kerrStationarySign_zero :
    kerrStationarySign 0 = -1 := by
  simp [kerrStationarySign]

@[simp] theorem kerrStationarySign_one :
    kerrStationarySign 1 = 1 := by
  simp [kerrStationarySign]

@[simp] theorem kerrStationarySign_two :
    kerrStationarySign 2 = 1 := by
  simp [kerrStationarySign]

@[simp] theorem kerrStationarySign_three :
    kerrStationarySign 3 = -1 := by
  simp [kerrStationarySign]

/-- The Christoffel symbols transform with the product of their three coordinate signs. -/
theorem kerrChristoffel_stationary_parity
    (r M a Q θ : ℝ)
    (ρ μ ν : Fin 4) :
    kerrStationarySign ρ *
        kerrStationarySign μ *
        kerrStationarySign ν *
        kerrChristoffel r M a Q θ ρ μ ν =
      kerrChristoffel r M a Q θ ρ μ ν := by
  fin_cases ρ <;> fin_cases μ <;> fin_cases ν <;>
    simp [kerrStationarySign, kerrChristoffel,
      kerrMetricInv, kerrMetricPartial, kerrCoordPartial,
      kerrMetricCov] <;> ring

/-- Hence every connection coefficient with odd stationary parity vanishes identically. -/
theorem kerrChristoffel_zero_of_odd_stationary
    (r M a Q θ : ℝ)
    (ρ μ ν : Fin 4)
    (hodd :
      kerrStationarySign ρ *
        kerrStationarySign μ *
        kerrStationarySign ν = -1) :
    kerrChristoffel r M a Q θ ρ μ ν = 0 := by
  have hp :=
    kerrChristoffel_stationary_parity r M a Q θ ρ μ ν
  rw [hodd] at hp
  linarith

/-! ### Meridional connection identities -/

/-- Trace `Γ^ρ_{μρ}` of the Levi-Civita connection. -/
def kerrChristoffelTrace
    (r M a Q θ : ℝ) (μ : Fin 4) : ℝ :=
  ∑ ρ : Fin 4, kerrChristoffel r M a Q θ ρ μ ρ

/-- Mixed contraction `Tr(Γ_r Γ_θ)` appearing in `R_{rθ}`. -/
def kerrConnectionCrossTrace
    (r M a Q θ : ℝ) : ℝ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4,
    kerrChristoffel r M a Q θ σ 1 ρ *
      kerrChristoffel r M a Q θ ρ 2 σ

/-- First simple meridional connection coefficient. -/
theorem kerrChristoffel_r_rtheta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffel r M a Q θ 1 1 2 =
      -a^2 * Real.cos θ * Real.sin θ /
        Sigma r a θ := by
  rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative]
  field_simp [hsig, hdel]
  ring

/-- Second simple meridional connection coefficient. -/
theorem kerrChristoffel_theta_rtheta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffel r M a Q θ 2 1 2 =
      r / Sigma r a θ := by
  rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative]
  field_simp [hsig, hdel]
  ring

/-- Radial connection trace equals the logarithmic radial derivative of
`sqrt(-g)=Σ sinθ`. -/
theorem kerrChristoffelTrace_r
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrChristoffelTrace r M a Q θ 1 =
      2 * r / Sigma r a θ := by
  unfold kerrChristoffelTrace
  simp_rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative]
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma kerrH
  nlinarith

/-- Polar connection trace equals the logarithmic polar derivative of
`sqrt(-g)=Σ sinθ`. -/
theorem kerrChristoffelTrace_theta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrChristoffelTrace r M a Q θ 2 =
      Real.cos θ / Real.sin θ -
        2 * a^2 * Real.cos θ * Real.sin θ /
          Sigma r a θ := by
  unfold kerrChristoffelTrace
  simp_rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative]
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma kerrH
  nlinarith

/-- The connection-product contraction in the mixed meridional Ricci component. -/
theorem kerrConnectionCrossTrace_formula
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrConnectionCrossTrace r M a Q θ =
      r * Real.cos θ *
        (5 * a^2 * (Real.cos θ)^2 - 4 * a^2 + r^2) /
        ((Sigma r a θ)^2 * Real.sin θ) := by
  unfold kerrConnectionCrossTrace
  simp_rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative]
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma kerrH
  nlinarith

/-! ### Stationary Ricci auxiliary scalar -/

/-- Compact numerator controlling the radial tt connection coefficient. -/
def kerrStationaryA (r M a Q θ : ℝ) : ℝ :=
  M * (r^2 - a^2 * (Real.cos θ)^2) - Q^2 * r

theorem kerrStationaryA_hasDerivAt_r
    (r M a Q θ : ℝ) :
    HasDerivAt (fun x : ℝ => kerrStationaryA x M a Q θ)
      (kerrH r M Q) r := by
  unfold kerrStationaryA kerrH
  convert ((((hasDerivAt_id r).pow 2).const_mul M).sub
    (hasDerivAt_const r (M * a^2 * (Real.cos θ)^2))).sub
    ((hasDerivAt_id r).const_mul (Q^2))) using 1 <;> ring

/-! ### Final phi-phi connection remainders -/

def kerrPhiPhiRadialRemainder
    (r M a Q θ : ℝ) : ℝ :=
  -r * Delta r M a Q * (Real.sin θ)^2 / Sigma r a θ

def kerrPhiPhiPolarRemainder
    (r M a Q θ : ℝ) : ℝ :=
  -a^2 * Real.cos θ * (Real.sin θ)^3 * kerrH r M Q /
      (Sigma r a θ)^2 -
    Real.cos θ * Real.sin θ * (r^2 + a^2) / Sigma r a θ

/-- The radial phi-phi connection is forced by the t-phi connection plus one
elementary square-form remainder. -/
theorem kerrChristoffel_r_phiphi_relation
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffel r M a Q θ 1 3 3 =
      -a * (Real.sin θ)^2 *
        kerrChristoffel r M a Q θ 1 0 3 +
      kerrPhiPhiRadialRemainder r M a Q θ := by
  rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel,
      kerrChristoffel_r_tphi r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular, kerrMetricRadialDerivative,
    kerrMetricPolarDerivative, kerrPhiPhiRadialRemainder,
    kerrStationaryA]
  field_simp [hsig, hdel]
  ring

/-- The polar phi-phi connection has the analogous forced decomposition. -/
theorem kerrChristoffel_theta_phiphi_relation
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffel r M a Q θ 2 3 3 =
      -a * (Real.sin θ)^2 *
        kerrChristoffel r M a Q θ 2 0 3 +
      kerrPhiPhiPolarRemainder r M a Q θ := by
  rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel,
      kerrChristoffel_theta_tphi r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular, kerrMetricRadialDerivative,
    kerrMetricPolarDerivative, kerrPhiPhiPolarRemainder, kerrH]
  field_simp [hsig, hdel]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Sigma
  nlinarith

/-! ### Stationary t-phi connection identities -/

theorem kerrChristoffel_r_tphi
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffel r M a Q θ 1 0 3 =
      -a * (Real.sin θ)^2 * Delta r M a Q *
        kerrStationaryA r M a Q θ / (Sigma r a θ)^3 := by
  rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative,
    kerrStationaryA]
  field_simp [hsig, hdel]
  ring

theorem kerrChristoffel_theta_tphi
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffel r M a Q θ 2 0 3 =
      a * Real.cos θ * Real.sin θ * (r^2 + a^2) *
        kerrH r M Q / (Sigma r a θ)^3 := by
  rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative,
    kerrH]
  field_simp [hsig, hdel]
  ring

/-! ### Stationary tt connection identities -/

theorem kerrChristoffel_r_tt
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffel r M a Q θ 1 0 0 =
      Delta r M a Q * kerrStationaryA r M a Q θ /
        (Sigma r a θ)^3 := by
  rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative,
    kerrStationaryA]
  field_simp [hsig, hdel]
  ring

theorem kerrChristoffel_theta_tt
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffel r M a Q θ 2 0 0 =
      -a^2 * Real.cos θ * Real.sin θ * kerrH r M Q /
        (Sigma r a θ)^3 := by
  rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative,
    kerrH]
  field_simp [hsig, hdel]
  ring

/-! ### Diagonal radial connection identities -/

/-- Radial connection coefficient entering the rr Ricci component. -/
theorem kerrChristoffel_r_rr
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffel r M a Q θ 1 1 1 =
      r / Sigma r a θ - (r - M) / Delta r M a Q := by
  rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative]
  field_simp [hsig, hdel]
  ring

/-- Polar connection coefficient entering the rr Ricci component. -/
theorem kerrChristoffel_theta_rr
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffel r M a Q θ 2 1 1 =
      a^2 * Real.cos θ * Real.sin θ /
        (Sigma r a θ * Delta r M a Q) := by
  rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative]
  field_simp [hsig, hdel]
  ring

/-! ### Diagonal polar connection identities -/

/-- Radial connection coefficient entering the theta-theta Ricci component. -/
theorem kerrChristoffel_r_thetatheta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffel r M a Q θ 1 2 2 =
      -r * Delta r M a Q / Sigma r a θ := by
  rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative]
  field_simp [hsig, hdel]
  ring

/-- Polar connection coefficient entering the theta-theta Ricci component. -/
theorem kerrChristoffel_theta_thetatheta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffel r M a Q θ 2 2 2 =
      -a^2 * Real.cos θ * Real.sin θ / Sigma r a θ := by
  rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative]
  field_simp [hsig, hdel]
  ring

/-- Quadratic connection contraction in the coordinate Ricci tensor. -/
def kerrConnectionProductTrace
    (r M a Q θ : ℝ) (μ ν : Fin 4) : ℝ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4,
    kerrChristoffel r M a Q θ σ μ ρ *
      kerrChristoffel r M a Q θ ρ ν σ

/-- Numerator of the quadratic connection correction relating the phi-phi and t-phi
Ricci blocks. -/
def kerrConnectionProductTracePhiCorrectionNumerator
    (r M a Q θ : ℝ) : ℝ :=
  -M * a^4 * (Real.cos θ)^6 * r -
    2 * M * a^4 * (Real.cos θ)^4 * r +
    3 * M * a^4 * (Real.cos θ)^2 * r -
    3 * M * a^2 * (Real.cos θ)^4 * r^3 +
    4 * M * a^2 * (Real.cos θ)^2 * r^3 - M * a^2 * r^3 +
    2 * M * (Real.cos θ)^2 * r^5 - 2 * M * r^5 +
    Q^2 * a^4 * (Real.cos θ)^6 - Q^2 * a^4 * (Real.cos θ)^2 +
    2 * Q^2 * a^2 * (Real.cos θ)^4 * r^2 -
    3 * Q^2 * a^2 * (Real.cos θ)^2 * r^2 + Q^2 * a^2 * r^2 -
    Q^2 * (Real.cos θ)^2 * r^4 + Q^2 * r^4 +
    a^6 * (Real.cos θ)^6 + 3 * a^4 * (Real.cos θ)^4 * r^2 +
    3 * a^2 * (Real.cos θ)^2 * r^4 + r^6

/-- The quadratic phi-phi contraction is not independent of the t-phi contraction. -/
theorem kerrConnectionProductTrace_phiphi_tphi_relation
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrConnectionProductTrace r M a Q θ 3 3 +
        a * (Real.sin θ)^2 *
          kerrConnectionProductTrace r M a Q θ 0 3 =
      -2 * kerrConnectionProductTracePhiCorrectionNumerator r M a Q θ /
        (Sigma r a θ)^3 := by
  unfold kerrConnectionProductTrace
  simp_rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular, kerrMetricRadialDerivative,
    kerrMetricPolarDerivative]
  unfold kerrConnectionProductTracePhiCorrectionNumerator
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma kerrH
  nlinarith

/-- Polynomial numerator of the quadratic connection contraction in R_tphi. -/
def kerrConnectionProductTraceTPhiNumerator
    (r M a Q θ : ℝ) : ℝ :=
  M^2 * a^4 * (Real.cos θ)^6 -
    M^2 * a^4 * (Real.cos θ)^4 -
    6 * M^2 * a^2 * (Real.cos θ)^4 * r^2 +
    6 * M^2 * a^2 * (Real.cos θ)^2 * r^2 +
    M^2 * (Real.cos θ)^2 * r^4 - M^2 * r^4 +
    6 * M * Q^2 * a^2 * (Real.cos θ)^4 * r -
    6 * M * Q^2 * a^2 * (Real.cos θ)^2 * r -
    2 * M * Q^2 * (Real.cos θ)^2 * r^3 + 2 * M * Q^2 * r^3 -
    M * a^4 * (Real.cos θ)^6 * r +
    3 * M * a^4 * (Real.cos θ)^4 * r +
    2 * M * a^2 * (Real.cos θ)^4 * r^3 +
    2 * M * a^2 * (Real.cos θ)^2 * r^3 +
    3 * M * (Real.cos θ)^2 * r^5 - M * r^5 -
    Q^4 * a^2 * (Real.cos θ)^4 +
    Q^4 * a^2 * (Real.cos θ)^2 + Q^4 * (Real.cos θ)^2 * r^2 -
    Q^4 * r^2 - Q^2 * a^4 * (Real.cos θ)^4 -
    2 * Q^2 * a^2 * (Real.cos θ)^4 * r^2 -
    2 * Q^2 * (Real.cos θ)^2 * r^4 + Q^2 * r^4

theorem kerrConnectionProductTrace_tphi_formula
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrConnectionProductTrace r M a Q θ 0 3 =
      2 * a * kerrConnectionProductTraceTPhiNumerator r M a Q θ /
        (Sigma r a θ)^4 := by
  unfold kerrConnectionProductTrace
  simp_rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative]
  unfold kerrConnectionProductTraceTPhiNumerator
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma kerrH
  nlinarith

/-- The quadratic connection contraction in R_tt collapses to two scalar squares. -/
theorem kerrConnectionProductTrace_tt_formula
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrConnectionProductTrace r M a Q θ 0 0 =
      2 * ((kerrStationaryA r M a Q θ)^2 -
        a^2 * (Real.cos θ)^2 * (kerrH r M Q)^2) /
          (Sigma r a θ)^4 := by
  unfold kerrConnectionProductTrace
  simp_rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative,
    kerrStationaryA, kerrH]
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma
  nlinarith

/-- Polynomial numerator of the quadratic connection contraction in R_rr. -/
def kerrConnectionProductTraceRRNumerator
    (r M a Q θ : ℝ) : ℝ :=
  M^2 * a^4 * (Real.cos θ)^4 -
    2 * M^2 * a^2 * (Real.cos θ)^2 * r^2 + 5 * M^2 * r^4 +
    2 * M * Q^2 * a^2 * (Real.cos θ)^2 * r - 6 * M * Q^2 * r^3 -
    4 * M * a^4 * (Real.cos θ)^4 * r +
    4 * M * a^4 * (Real.cos θ)^2 * r - 4 * M * a^2 * r^3 -
    4 * M * r^5 + 2 * Q^4 * r^2 +
    Q^2 * a^4 * (Real.cos θ)^4 - Q^2 * a^4 * (Real.cos θ)^2 -
    Q^2 * a^2 * (Real.cos θ)^2 * r^2 + 3 * Q^2 * a^2 * r^2 +
    2 * Q^2 * r^4 + a^6 * (Real.cos θ)^4 -
    a^6 * (Real.cos θ)^2 + 2 * a^4 * (Real.cos θ)^4 * r^2 -
    2 * a^4 * (Real.cos θ)^2 * r^2 + a^4 * r^2 +
    a^2 * (Real.cos θ)^2 * r^4 + a^2 * r^4 + r^6

/-- Full quadratic connection contraction in the radial diagonal Ricci component. -/
theorem kerrConnectionProductTrace_rr_formula
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrConnectionProductTrace r M a Q θ 1 1 =
      2 * kerrConnectionProductTraceRRNumerator r M a Q θ /
        ((Sigma r a θ)^2 * (Delta r M a Q)^2) := by
  unfold kerrConnectionProductTrace
  simp_rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative]
  unfold kerrConnectionProductTraceRRNumerator
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma kerrH
  nlinarith

/-- Full quadratic connection contraction in the polar diagonal Ricci component. -/
theorem kerrConnectionProductTrace_thetatheta_formula
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrConnectionProductTrace r M a Q θ 2 2 =
      (-4 * M * a^2 * (Real.cos θ)^4 * r +
        4 * M * a^2 * (Real.cos θ)^2 * r -
        4 * M * (Real.cos θ)^2 * r^3 + 4 * M * r^3 +
        2 * Q^2 * a^2 * (Real.cos θ)^4 -
        2 * Q^2 * a^2 * (Real.cos θ)^2 +
        2 * Q^2 * (Real.cos θ)^2 * r^2 - 2 * Q^2 * r^2 +
        3 * a^4 * (Real.cos θ)^6 - 4 * a^4 * (Real.cos θ)^4 +
        2 * a^4 * (Real.cos θ)^2 +
        2 * a^2 * (Real.cos θ)^4 * r^2 +
        2 * a^2 * (Real.cos θ)^2 * r^2 - 2 * a^2 * r^2 +
        3 * (Real.cos θ)^2 * r^4 - 2 * r^4) /
      ((Real.sin θ)^2 * (Sigma r a θ)^2) := by
  unfold kerrConnectionProductTrace
  simp_rw [kerrChristoffel_eq_regular r M a Q θ hsig hdel]
  simp [kerrChristoffelRegular, kerrMetricInv,
    kerrMetricDerivativeRegular,
    kerrMetricRadialDerivative, kerrMetricPolarDerivative]
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma kerrH
  nlinarith

/-- Coordinate derivative of a Christoffel symbol. -/
def kerrChristoffelPartial
    (κ : Fin 4) (r M a Q θ : ℝ)
    (ρ μ ν : Fin 4) : ℝ :=
  kerrCoordPartial κ
    (fun rr th => kerrChristoffel rr M a Q th ρ μ ν) r θ

/-! ### Local second-derivative transfer on the regular Kerr chart -/

/-- Radial derivative of the simple meridional Christoffel
`Γ^r_{rθ}=-a² sinθ cosθ/Σ`. -/
theorem kerrChristoffel_r_rtheta_hasDerivAt_r
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffel x M a Q θ 1 1 2)
      (2 * a^2 * r * Real.cos θ * Real.sin θ /
        (Sigma r a θ)^2) r := by
  have hn :
      HasDerivAt
        (fun _ : ℝ => -a^2 * Real.cos θ * Real.sin θ)
        0 r :=
    hasDerivAt_const r
      (-a^2 * Real.cos θ * Real.sin θ)
  have hreg :=
    hn.fun_div (Sigma_hasDerivAt_r r a θ) hsig
  have hreg' :
      HasDerivAt
        (fun x : ℝ =>
          -a^2 * Real.cos θ * Real.sin θ / Sigma x a θ)
        (2 * a^2 * r * Real.cos θ * Real.sin θ /
          (Sigma r a θ)^2) r := by
    convert hreg using 1
    field_simp [hsig]
    ring
  have hS :=
    (Sigma_hasDerivAt_r r a θ).continuousAt.eventually_ne hsig
  have hD :=
    (Delta_hasDerivAt_r r M a Q).continuousAt.eventually_ne hdel
  have heq :
      (fun x : ℝ => kerrChristoffel x M a Q θ 1 1 2) =ᶠ[𝓝 r]
        (fun x : ℝ =>
          -a^2 * Real.cos θ * Real.sin θ / Sigma x a θ) := by
    filter_upwards [hS, hD] with x hxS hxD
    exact kerrChristoffel_r_rtheta x M a Q θ hxS hxD
  exact hreg'.congr_of_eventuallyEq heq

/-- Polar derivative of `Γ^θ_{rθ}=r/Σ`. -/
theorem kerrChristoffel_theta_rtheta_hasDerivAt_theta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffel r M a Q x 2 1 2)
      (2 * a^2 * r * Real.cos θ * Real.sin θ /
        (Sigma r a θ)^2) θ := by
  have hn :
      HasDerivAt (fun _ : ℝ => r) 0 θ :=
    hasDerivAt_const θ r
  have hreg :=
    hn.fun_div (Sigma_hasDerivAt_theta r a θ) hsig
  have hreg' :
      HasDerivAt
        (fun x : ℝ => r / Sigma r a x)
        (2 * a^2 * r * Real.cos θ * Real.sin θ /
          (Sigma r a θ)^2) θ := by
    convert hreg using 1
    field_simp [hsig]
    ring
  have hS :=
    (Sigma_hasDerivAt_theta r a θ).continuousAt.eventually_ne hsig
  have heq :
      (fun x : ℝ => kerrChristoffel r M a Q x 2 1 2) =ᶠ[𝓝 θ]
        (fun x : ℝ => r / Sigma r a x) := by
    filter_upwards [hS] with x hxS
    exact kerrChristoffel_theta_rtheta
      r M a Q x hxS hdel
  exact hreg'.congr_of_eventuallyEq heq

/-- Polar derivative of the radial connection trace `2r/Σ`. -/
theorem kerrChristoffelTrace_r_hasDerivAt_theta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffelTrace r M a Q x 1)
      (4 * a^2 * r * Real.cos θ * Real.sin θ /
        (Sigma r a θ)^2) θ := by
  have hn :
      HasDerivAt (fun _ : ℝ => 2 * r) 0 θ :=
    hasDerivAt_const θ (2 * r)
  have hreg :=
    hn.fun_div (Sigma_hasDerivAt_theta r a θ) hsig
  have hreg' :
      HasDerivAt
        (fun x : ℝ => 2 * r / Sigma r a x)
        (4 * a^2 * r * Real.cos θ * Real.sin θ /
          (Sigma r a θ)^2) θ := by
    convert hreg using 1
    field_simp [hsig]
    ring
  have hS :=
    (Sigma_hasDerivAt_theta r a θ).continuousAt.eventually_ne hsig
  have hSin :=
    (Real.hasDerivAt_sin θ).continuousAt.eventually_ne hsin
  have heq :
      (fun x : ℝ => kerrChristoffelTrace r M a Q x 1) =ᶠ[𝓝 θ]
        (fun x : ℝ => 2 * r / Sigma r a x) := by
    filter_upwards [hS, hSin] with x hxS hxSin
    exact kerrChristoffelTrace_r
      r M a Q x hxS hdel hxSin
  exact hreg'.congr_of_eventuallyEq heq

/-- The coordinate partials entering `R_{rθ}` are therefore explicit. -/
theorem kerrChristoffelPartial_r_rtheta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffelPartial 1 r M a Q θ 1 1 2 =
      2 * a^2 * r * Real.cos θ * Real.sin θ /
        (Sigma r a θ)^2 := by
  unfold kerrChristoffelPartial kerrCoordPartial
  simpa using
    (kerrChristoffel_r_rtheta_hasDerivAt_r
      r M a Q θ hsig hdel).deriv

theorem kerrChristoffelPartial_theta_rtheta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffelPartial 2 r M a Q θ 2 1 2 =
      2 * a^2 * r * Real.cos θ * Real.sin θ /
        (Sigma r a θ)^2 := by
  unfold kerrChristoffelPartial kerrCoordPartial
  simpa using
    (kerrChristoffel_theta_rtheta_hasDerivAt_theta
      r M a Q θ hsig hdel).deriv

theorem kerrChristoffelTracePartial_theta_r
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrCoordPartial 2
      (fun rr th => kerrChristoffelTrace rr M a Q th 1)
      r θ =
      4 * a^2 * r * Real.cos θ * Real.sin θ /
        (Sigma r a θ)^2 := by
  unfold kerrCoordPartial
  simpa using
    (kerrChristoffelTrace_r_hasDerivAt_theta
      r M a Q θ hsig hdel hsin).deriv

/-- Radial derivative of the polar connection trace. -/
theorem kerrChristoffelTrace_theta_hasDerivAt_r
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffelTrace x M a Q θ 2)
      (4 * a^2 * r * Real.cos θ * Real.sin θ /
        (Sigma r a θ)^2) r := by
  have hfirst :
      HasDerivAt
        (fun _ : ℝ => Real.cos θ / Real.sin θ)
        0 r :=
    hasDerivAt_const r (Real.cos θ / Real.sin θ)
  have hn :
      HasDerivAt
        (fun _ : ℝ =>
          -2 * a^2 * Real.cos θ * Real.sin θ)
        0 r :=
    hasDerivAt_const r
      (-2 * a^2 * Real.cos θ * Real.sin θ)
  have hfrac :=
    hn.fun_div (Sigma_hasDerivAt_r r a θ) hsig
  have hreg := hfirst.add hfrac
  have hreg' :
      HasDerivAt
        (fun x : ℝ =>
          Real.cos θ / Real.sin θ -
            2 * a^2 * Real.cos θ * Real.sin θ /
              Sigma x a θ)
        (4 * a^2 * r * Real.cos θ * Real.sin θ /
          (Sigma r a θ)^2) r := by
    convert hreg using 1
    field_simp [hsig, hsin]
    ring
  have hS :=
    (Sigma_hasDerivAt_r r a θ).continuousAt.eventually_ne hsig
  have hD :=
    (Delta_hasDerivAt_r r M a Q).continuousAt.eventually_ne hdel
  have heq :
      (fun x : ℝ => kerrChristoffelTrace x M a Q θ 2) =ᶠ[𝓝 r]
        (fun x : ℝ =>
          Real.cos θ / Real.sin θ -
            2 * a^2 * Real.cos θ * Real.sin θ /
              Sigma x a θ) := by
    filter_upwards [hS, hD] with x hxS hxD
    exact kerrChristoffelTrace_theta
      x M a Q θ hxS hxD hsin
  exact hreg'.congr_of_eventuallyEq heq

theorem kerrChristoffelTracePartial_r_theta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrCoordPartial 1
      (fun rr th => kerrChristoffelTrace rr M a Q th 2)
      r θ =
      4 * a^2 * r * Real.cos θ * Real.sin θ /
        (Sigma r a θ)^2 := by
  unfold kerrCoordPartial
  simpa using
    (kerrChristoffelTrace_theta_hasDerivAt_r
      r M a Q θ hsig hdel hsin).deriv

/-! ### Final phi-phi derivative transfer -/

theorem kerrPhiPhiRadialRemainder_hasDerivAt_r
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrPhiPhiRadialRemainder x M a Q θ)
      ((Real.sin θ)^2 *
        (-(Delta r M a Q + 2 * r * (r - M)) * Sigma r a θ +
          2 * r^2 * Delta r M a Q) / (Sigma r a θ)^2) r := by
  unfold kerrPhiPhiRadialRemainder
  have hnum :
      HasDerivAt
        (fun x : ℝ => -x * Delta x M a Q * (Real.sin θ)^2)
        (-(Delta r M a Q + 2 * r * (r - M)) * (Real.sin θ)^2) r := by
    convert (((hasDerivAt_id r).mul
      (Delta_hasDerivAt_r r M a Q)).neg.const_mul
        ((Real.sin θ)^2)) using 1 <;> ring
  have hreg := hnum.fun_div (Sigma_hasDerivAt_r r a θ) hsig
  convert hreg using 1 <;> field_simp [hsig] <;> ring

theorem kerrPhiPhiPolarRemainder_hasDerivAt_theta
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrPhiPhiPolarRemainder r M a Q x)
      ((a^2 * kerrH r M Q * (Real.sin θ)^2 *
          ((Real.sin θ)^2 - 3 * (Real.cos θ)^2) * Sigma r a θ -
        4 * a^4 * kerrH r M Q * (Real.cos θ)^2 *
          (Real.sin θ)^4) / (Sigma r a θ)^3 +
       ((r^2 + a^2) * ((Real.sin θ)^2 - (Real.cos θ)^2) *
          Sigma r a θ -
        2 * a^2 * (r^2 + a^2) * (Real.cos θ)^2 *
          (Real.sin θ)^2) / (Sigma r a θ)^2) θ := by
  unfold kerrPhiPhiPolarRemainder
  have hcs3 := (Real.hasDerivAt_cos θ).mul
    ((Real.hasDerivAt_sin θ).pow 3)
  have hnum1 := hcs3.const_mul (-a^2 * kerrH r M Q)
  have hden2 := (Sigma_hasDerivAt_theta r a θ).pow 2
  have hterm1 := hnum1.fun_div hden2 (pow_ne_zero 2 hsig)
  have hcs := (Real.hasDerivAt_cos θ).mul (Real.hasDerivAt_sin θ)
  have hnum2 := hcs.const_mul (-(r^2 + a^2))
  have hterm2 := hnum2.fun_div (Sigma_hasDerivAt_theta r a θ) hsig
  have hreg := hterm1.add hterm2
  convert hreg using 1 <;> field_simp [hsig] <;> ring

/-- Radial derivative relation for the last stationary connection coefficient. -/
theorem kerrChristoffelPartial_r_phiphi_relation
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffelPartial 1 r M a Q θ 1 3 3 =
      -a * (Real.sin θ)^2 *
        kerrChristoffelPartial 1 r M a Q θ 1 0 3 +
      (Real.sin θ)^2 *
        (-(Delta r M a Q + 2 * r * (r - M)) * Sigma r a θ +
          2 * r^2 * Delta r M a Q) / (Sigma r a θ)^2 := by
  have hbase := (kerrChristoffel_r_tphi_hasDerivAt_r
    r M a Q θ hsig hdel).const_mul (-a * (Real.sin θ)^2)
  have hrem := kerrPhiPhiRadialRemainder_hasDerivAt_r
    r M a Q θ hsig
  have hsum := hbase.add hrem
  have hS := (Sigma_hasDerivAt_r r a θ).continuousAt.eventually_ne hsig
  have hD := (Delta_hasDerivAt_r r M a Q).continuousAt.eventually_ne hdel
  have heq :
      (fun x : ℝ => kerrChristoffel x M a Q θ 1 3 3) =ᶠ[𝓝 r]
        (fun x : ℝ => -a * (Real.sin θ)^2 *
          kerrChristoffel x M a Q θ 1 0 3 +
          kerrPhiPhiRadialRemainder x M a Q θ) := by
    filter_upwards [hS, hD] with x hxS hxD
    exact kerrChristoffel_r_phiphi_relation x M a Q θ hxS hxD
  have hfinal := hsum.congr_of_eventuallyEq heq.symm
  unfold kerrChristoffelPartial kerrCoordPartial
  simpa using hfinal.deriv

/-- Polar derivative relation for the last stationary connection coefficient. -/
theorem kerrChristoffelPartial_theta_phiphi_relation
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffelPartial 2 r M a Q θ 2 3 3 =
      -a * (Real.sin θ)^2 *
        kerrChristoffelPartial 2 r M a Q θ 2 0 3 -
      2 * a * Real.sin θ * Real.cos θ *
        kerrChristoffel r M a Q θ 2 0 3 +
      ((a^2 * kerrH r M Q * (Real.sin θ)^2 *
          ((Real.sin θ)^2 - 3 * (Real.cos θ)^2) * Sigma r a θ -
        4 * a^4 * kerrH r M Q * (Real.cos θ)^2 *
          (Real.sin θ)^4) / (Sigma r a θ)^3 +
       ((r^2 + a^2) * ((Real.sin θ)^2 - (Real.cos θ)^2) *
          Sigma r a θ -
        2 * a^2 * (r^2 + a^2) * (Real.cos θ)^2 *
          (Real.sin θ)^2) / (Sigma r a θ)^2) := by
  have hf := ((Real.hasDerivAt_sin θ).pow 2).const_mul (-a)
  have hg := kerrChristoffel_theta_tphi_hasDerivAt_theta
    r M a Q θ hsig hdel
  have hprod := hf.mul hg
  have hrem := kerrPhiPhiPolarRemainder_hasDerivAt_theta
    r M a Q θ hsig
  have hsum := hprod.add hrem
  have hS := (Sigma_hasDerivAt_theta r a θ).continuousAt.eventually_ne hsig
  have heq :
      (fun x : ℝ => kerrChristoffel r M a Q x 2 3 3) =ᶠ[𝓝 θ]
        (fun x : ℝ => -a * (Real.sin x)^2 *
          kerrChristoffel r M a Q x 2 0 3 +
          kerrPhiPhiPolarRemainder r M a Q x) := by
    filter_upwards [hS] with x hxS
    exact kerrChristoffel_theta_phiphi_relation r M a Q x hxS hdel
  have hfinal := hsum.congr_of_eventuallyEq heq.symm
  unfold kerrChristoffelPartial kerrCoordPartial
  convert hfinal.deriv using 1 <;> ring

/-! ### Stationary t-phi second-derivative transfer -/

theorem kerrChristoffel_r_tphi_hasDerivAt_r
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffel x M a Q θ 1 0 3)
      (-a * (Real.sin θ)^2 *
        (((2 * (r - M) * kerrStationaryA r M a Q θ +
            Delta r M a Q * kerrH r M Q) * Sigma r a θ -
          6 * r * Delta r M a Q * kerrStationaryA r M a Q θ) /
            (Sigma r a θ)^4)) r := by
  have hnum := (Delta_hasDerivAt_r r M a Q).mul
    (kerrStationaryA_hasDerivAt_r r M a Q θ)
  have hden := (Sigma_hasDerivAt_r r a θ).pow 3
  have hquot := hnum.fun_div hden (pow_ne_zero 3 hsig)
  have hreg := hquot.const_mul (-a * (Real.sin θ)^2)
  have hreg' :
      HasDerivAt
        (fun x : ℝ => -a * (Real.sin θ)^2 * Delta x M a Q *
          kerrStationaryA x M a Q θ / (Sigma x a θ)^3)
        (-a * (Real.sin θ)^2 *
          (((2 * (r - M) * kerrStationaryA r M a Q θ +
              Delta r M a Q * kerrH r M Q) * Sigma r a θ -
            6 * r * Delta r M a Q * kerrStationaryA r M a Q θ) /
              (Sigma r a θ)^4)) r := by
    convert hreg using 1 <;> field_simp [hsig] <;> ring
  have hS := (Sigma_hasDerivAt_r r a θ).continuousAt.eventually_ne hsig
  have hD := (Delta_hasDerivAt_r r M a Q).continuousAt.eventually_ne hdel
  have heq :
      (fun x : ℝ => kerrChristoffel x M a Q θ 1 0 3) =ᶠ[𝓝 r]
        (fun x : ℝ => -a * (Real.sin θ)^2 * Delta x M a Q *
          kerrStationaryA x M a Q θ / (Sigma x a θ)^3) := by
    filter_upwards [hS, hD] with x hxS hxD
    exact kerrChristoffel_r_tphi x M a Q θ hxS hxD
  exact hreg'.congr_of_eventuallyEq heq

theorem kerrChristoffel_theta_tphi_hasDerivAt_theta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffel r M a Q x 2 0 3)
      (a * (r^2 + a^2) * kerrH r M Q *
        (((Real.cos θ)^2 - (Real.sin θ)^2) * Sigma r a θ +
          6 * a^2 * (Real.cos θ)^2 * (Real.sin θ)^2) /
            (Sigma r a θ)^4)) θ := by
  have hcs := (Real.hasDerivAt_cos θ).mul (Real.hasDerivAt_sin θ)
  have hnum := hcs.const_mul (a * (r^2 + a^2) * kerrH r M Q)
  have hden := (Sigma_hasDerivAt_theta r a θ).pow 3
  have hreg := hnum.fun_div hden (pow_ne_zero 3 hsig)
  have hreg' :
      HasDerivAt
        (fun x : ℝ => a * Real.cos x * Real.sin x * (r^2 + a^2) *
          kerrH r M Q / (Sigma r a x)^3)
        (a * (r^2 + a^2) * kerrH r M Q *
          (((Real.cos θ)^2 - (Real.sin θ)^2) * Sigma r a θ +
            6 * a^2 * (Real.cos θ)^2 * (Real.sin θ)^2) /
              (Sigma r a θ)^4)) θ := by
    convert hreg using 1 <;> field_simp [hsig] <;> ring
  have hS := (Sigma_hasDerivAt_theta r a θ).continuousAt.eventually_ne hsig
  have heq :
      (fun x : ℝ => kerrChristoffel r M a Q x 2 0 3) =ᶠ[𝓝 θ]
        (fun x : ℝ => a * Real.cos x * Real.sin x * (r^2 + a^2) *
          kerrH r M Q / (Sigma r a x)^3) := by
    filter_upwards [hS] with x hxS
    exact kerrChristoffel_theta_tphi r M a Q x hxS hdel
  exact hreg'.congr_of_eventuallyEq heq

theorem kerrChristoffelPartial_r_tphi
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffelPartial 1 r M a Q θ 1 0 3 =
      -a * (Real.sin θ)^2 *
        (((2 * (r - M) * kerrStationaryA r M a Q θ +
            Delta r M a Q * kerrH r M Q) * Sigma r a θ -
          6 * r * Delta r M a Q * kerrStationaryA r M a Q θ) /
            (Sigma r a θ)^4) := by
  unfold kerrChristoffelPartial kerrCoordPartial
  simpa using
    (kerrChristoffel_r_tphi_hasDerivAt_r r M a Q θ hsig hdel).deriv

theorem kerrChristoffelPartial_theta_tphi
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffelPartial 2 r M a Q θ 2 0 3 =
      a * (r^2 + a^2) * kerrH r M Q *
        (((Real.cos θ)^2 - (Real.sin θ)^2) * Sigma r a θ +
          6 * a^2 * (Real.cos θ)^2 * (Real.sin θ)^2) /
            (Sigma r a θ)^4) := by
  unfold kerrChristoffelPartial kerrCoordPartial
  simpa using
    (kerrChristoffel_theta_tphi_hasDerivAt_theta
      r M a Q θ hsig hdel).deriv

/-! ### Stationary tt second-derivative transfer -/

theorem kerrChristoffel_r_tt_hasDerivAt_r
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffel x M a Q θ 1 0 0)
      (((2 * (r - M) * kerrStationaryA r M a Q θ +
          Delta r M a Q * kerrH r M Q) * Sigma r a θ -
        6 * r * Delta r M a Q * kerrStationaryA r M a Q θ) /
          (Sigma r a θ)^4) r := by
  have hnum := (Delta_hasDerivAt_r r M a Q).mul
    (kerrStationaryA_hasDerivAt_r r M a Q θ)
  have hden := (Sigma_hasDerivAt_r r a θ).pow 3
  have hreg := hnum.fun_div hden (pow_ne_zero 3 hsig)
  have hreg' :
      HasDerivAt
        (fun x : ℝ => Delta x M a Q * kerrStationaryA x M a Q θ /
          (Sigma x a θ)^3)
        (((2 * (r - M) * kerrStationaryA r M a Q θ +
            Delta r M a Q * kerrH r M Q) * Sigma r a θ -
          6 * r * Delta r M a Q * kerrStationaryA r M a Q θ) /
            (Sigma r a θ)^4) r := by
    convert hreg using 1 <;> field_simp [hsig] <;> ring
  have hS := (Sigma_hasDerivAt_r r a θ).continuousAt.eventually_ne hsig
  have hD := (Delta_hasDerivAt_r r M a Q).continuousAt.eventually_ne hdel
  have heq :
      (fun x : ℝ => kerrChristoffel x M a Q θ 1 0 0) =ᶠ[𝓝 r]
        (fun x : ℝ => Delta x M a Q * kerrStationaryA x M a Q θ /
          (Sigma x a θ)^3) := by
    filter_upwards [hS, hD] with x hxS hxD
    exact kerrChristoffel_r_tt x M a Q θ hxS hxD
  exact hreg'.congr_of_eventuallyEq heq

theorem kerrChristoffel_theta_tt_hasDerivAt_theta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffel r M a Q x 2 0 0)
      ((a^2 * ((Real.sin θ)^2 - (Real.cos θ)^2) *
          kerrH r M Q * Sigma r a θ -
        6 * a^4 * (Real.cos θ)^2 * (Real.sin θ)^2 *
          kerrH r M Q) / (Sigma r a θ)^4) θ := by
  have hcs := (Real.hasDerivAt_cos θ).mul (Real.hasDerivAt_sin θ)
  have hnum := hcs.const_mul (-a^2 * kerrH r M Q)
  have hden := (Sigma_hasDerivAt_theta r a θ).pow 3
  have hreg := hnum.fun_div hden (pow_ne_zero 3 hsig)
  have hreg' :
      HasDerivAt
        (fun x : ℝ => -a^2 * Real.cos x * Real.sin x * kerrH r M Q /
          (Sigma r a x)^3)
        ((a^2 * ((Real.sin θ)^2 - (Real.cos θ)^2) *
            kerrH r M Q * Sigma r a θ -
          6 * a^4 * (Real.cos θ)^2 * (Real.sin θ)^2 *
            kerrH r M Q) / (Sigma r a θ)^4) θ := by
    convert hreg using 1 <;> field_simp [hsig] <;> ring
  have hS := (Sigma_hasDerivAt_theta r a θ).continuousAt.eventually_ne hsig
  have heq :
      (fun x : ℝ => kerrChristoffel r M a Q x 2 0 0) =ᶠ[𝓝 θ]
        (fun x : ℝ => -a^2 * Real.cos x * Real.sin x * kerrH r M Q /
          (Sigma r a x)^3) := by
    filter_upwards [hS] with x hxS
    exact kerrChristoffel_theta_tt r M a Q x hxS hdel
  exact hreg'.congr_of_eventuallyEq heq

theorem kerrChristoffelPartial_r_tt
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffelPartial 1 r M a Q θ 1 0 0 =
      ((2 * (r - M) * kerrStationaryA r M a Q θ +
          Delta r M a Q * kerrH r M Q) * Sigma r a θ -
        6 * r * Delta r M a Q * kerrStationaryA r M a Q θ) /
          (Sigma r a θ)^4 := by
  unfold kerrChristoffelPartial kerrCoordPartial
  simpa using (kerrChristoffel_r_tt_hasDerivAt_r r M a Q θ hsig hdel).deriv

theorem kerrChristoffelPartial_theta_tt
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffelPartial 2 r M a Q θ 2 0 0 =
      (a^2 * ((Real.sin θ)^2 - (Real.cos θ)^2) *
          kerrH r M Q * Sigma r a θ -
        6 * a^4 * (Real.cos θ)^2 * (Real.sin θ)^2 *
          kerrH r M Q) / (Sigma r a θ)^4 := by
  unfold kerrChristoffelPartial kerrCoordPartial
  simpa using
    (kerrChristoffel_theta_tt_hasDerivAt_theta r M a Q θ hsig hdel).deriv

/-! ### Radial diagonal second-derivative transfer -/

/-- Radial derivative of Gamma^r_rr on the regular chart. -/
theorem kerrChristoffel_r_rr_hasDerivAt_r
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffel x M a Q θ 1 1 1)
      ((Sigma r a θ - 2 * r^2) / (Sigma r a θ)^2 -
        (Delta r M a Q - 2 * (r - M)^2) /
          (Delta r M a Q)^2) r := by
  have hleft := (hasDerivAt_id r).fun_div
    (Sigma_hasDerivAt_r r a θ) hsig
  have hnum : HasDerivAt (fun x : ℝ => x - M) 1 r := by
    simpa using (hasDerivAt_id r).sub_const M
  have hright := hnum.fun_div (Delta_hasDerivAt_r r M a Q) hdel
  have hreg := hleft.sub hright
  have hreg' :
      HasDerivAt
        (fun x : ℝ => x / Sigma x a θ - (x - M) / Delta x M a Q)
        ((Sigma r a θ - 2 * r^2) / (Sigma r a θ)^2 -
          (Delta r M a Q - 2 * (r - M)^2) /
            (Delta r M a Q)^2) r := by
    convert hreg using 1 <;> field_simp [hsig, hdel] <;> ring
  have hS := (Sigma_hasDerivAt_r r a θ).continuousAt.eventually_ne hsig
  have hD := (Delta_hasDerivAt_r r M a Q).continuousAt.eventually_ne hdel
  have heq :
      (fun x : ℝ => kerrChristoffel x M a Q θ 1 1 1) =ᶠ[𝓝 r]
        (fun x : ℝ => x / Sigma x a θ - (x - M) / Delta x M a Q) := by
    filter_upwards [hS, hD] with x hxS hxD
    exact kerrChristoffel_r_rr x M a Q θ hxS hxD
  exact hreg'.congr_of_eventuallyEq heq

/-- Polar derivative of Gamma^theta_rr on the regular chart. -/
theorem kerrChristoffel_theta_rr_hasDerivAt_theta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffel r M a Q x 2 1 1)
      ((a^2 * ((Real.cos θ)^2 - (Real.sin θ)^2) * Sigma r a θ +
          2 * a^4 * (Real.cos θ)^2 * (Real.sin θ)^2) /
        ((Sigma r a θ)^2 * Delta r M a Q)) θ := by
  have hcs := (Real.hasDerivAt_cos θ).mul (Real.hasDerivAt_sin θ)
  have hnum := hcs.const_mul (a^2)
  have hfrac := hnum.fun_div (Sigma_hasDerivAt_theta r a θ) hsig
  have hreg := hfrac.const_mul (Delta r M a Q)⁻¹
  have hreg' :
      HasDerivAt
        (fun x : ℝ =>
          a^2 * Real.cos x * Real.sin x /
            (Sigma r a x * Delta r M a Q))
        ((a^2 * ((Real.cos θ)^2 - (Real.sin θ)^2) * Sigma r a θ +
            2 * a^4 * (Real.cos θ)^2 * (Real.sin θ)^2) /
          ((Sigma r a θ)^2 * Delta r M a Q)) θ := by
    convert hreg using 1 <;> field_simp [hsig, hdel] <;> ring
  have hS := (Sigma_hasDerivAt_theta r a θ).continuousAt.eventually_ne hsig
  have heq :
      (fun x : ℝ => kerrChristoffel r M a Q x 2 1 1) =ᶠ[𝓝 θ]
        (fun x : ℝ =>
          a^2 * Real.cos x * Real.sin x /
            (Sigma r a x * Delta r M a Q)) := by
    filter_upwards [hS] with x hxS
    exact kerrChristoffel_theta_rr r M a Q x hxS hdel
  exact hreg'.congr_of_eventuallyEq heq

/-- Radial derivative of the radial connection trace. -/
theorem kerrChristoffelTrace_r_hasDerivAt_r
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffelTrace x M a Q θ 1)
      ((2 * Sigma r a θ - 4 * r^2) / (Sigma r a θ)^2) r := by
  have hnum := (hasDerivAt_id r).const_mul 2
  have hreg := hnum.fun_div (Sigma_hasDerivAt_r r a θ) hsig
  have hreg' :
      HasDerivAt (fun x : ℝ => 2 * x / Sigma x a θ)
        ((2 * Sigma r a θ - 4 * r^2) / (Sigma r a θ)^2) r := by
    convert hreg using 1 <;> field_simp [hsig] <;> ring
  have hS := (Sigma_hasDerivAt_r r a θ).continuousAt.eventually_ne hsig
  have hD := (Delta_hasDerivAt_r r M a Q).continuousAt.eventually_ne hdel
  have heq :
      (fun x : ℝ => kerrChristoffelTrace x M a Q θ 1) =ᶠ[𝓝 r]
        (fun x : ℝ => 2 * x / Sigma x a θ) := by
    filter_upwards [hS, hD] with x hxS hxD
    exact kerrChristoffelTrace_r x M a Q θ hxS hxD hsin
  exact hreg'.congr_of_eventuallyEq heq

theorem kerrChristoffelPartial_r_rr
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffelPartial 1 r M a Q θ 1 1 1 =
      (Sigma r a θ - 2 * r^2) / (Sigma r a θ)^2 -
      (Delta r M a Q - 2 * (r - M)^2) / (Delta r M a Q)^2 := by
  unfold kerrChristoffelPartial kerrCoordPartial
  simpa using (kerrChristoffel_r_rr_hasDerivAt_r r M a Q θ hsig hdel).deriv

theorem kerrChristoffelPartial_theta_rr
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffelPartial 2 r M a Q θ 2 1 1 =
      (a^2 * ((Real.cos θ)^2 - (Real.sin θ)^2) * Sigma r a θ +
        2 * a^4 * (Real.cos θ)^2 * (Real.sin θ)^2) /
        ((Sigma r a θ)^2 * Delta r M a Q) := by
  unfold kerrChristoffelPartial kerrCoordPartial
  simpa using
    (kerrChristoffel_theta_rr_hasDerivAt_theta r M a Q θ hsig hdel).deriv

theorem kerrChristoffelTracePartial_r_r
    (r M a Q θ : ℝ) (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) (hsin : Real.sin θ ≠ 0) :
    kerrCoordPartial 1
      (fun rr th => kerrChristoffelTrace rr M a Q th 1) r θ =
      (2 * Sigma r a θ - 4 * r^2) / (Sigma r a θ)^2 := by
  unfold kerrCoordPartial
  simpa using
    (kerrChristoffelTrace_r_hasDerivAt_r r M a Q θ hsig hdel hsin).deriv

/-! ### Polar diagonal second-derivative transfer -/

/-- Radial derivative of Gamma^r_{theta theta} on the regular chart. -/
theorem kerrChristoffel_r_thetatheta_hasDerivAt_r
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffel x M a Q θ 1 2 2)
      (((-Delta r M a Q - 2 * r * (r - M)) * Sigma r a θ +
          2 * r^2 * Delta r M a Q) / (Sigma r a θ)^2) r := by
  have hnum :
      HasDerivAt
        (fun x : ℝ => -x * Delta x M a Q)
        (-Delta r M a Q - 2 * r * (r - M)) r := by
    convert ((hasDerivAt_id r).mul
      (Delta_hasDerivAt_r r M a Q)).neg using 1 <;> ring
  have hreg := hnum.fun_div (Sigma_hasDerivAt_r r a θ) hsig
  have hreg' :
      HasDerivAt
        (fun x : ℝ => -x * Delta x M a Q / Sigma x a θ)
        (((-Delta r M a Q - 2 * r * (r - M)) * Sigma r a θ +
            2 * r^2 * Delta r M a Q) / (Sigma r a θ)^2) r := by
    convert hreg using 1
    field_simp [hsig]
    ring
  have hS :=
    (Sigma_hasDerivAt_r r a θ).continuousAt.eventually_ne hsig
  have hD :=
    (Delta_hasDerivAt_r r M a Q).continuousAt.eventually_ne hdel
  have heq :
      (fun x : ℝ => kerrChristoffel x M a Q θ 1 2 2) =ᶠ[𝓝 r]
        (fun x : ℝ => -x * Delta x M a Q / Sigma x a θ) := by
    filter_upwards [hS, hD] with x hxS hxD
    exact kerrChristoffel_r_thetatheta x M a Q θ hxS hxD
  exact hreg'.congr_of_eventuallyEq heq

/-- Polar derivative of Gamma^theta_{theta theta} on the regular chart. -/
theorem kerrChristoffel_theta_thetatheta_hasDerivAt_theta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffel r M a Q x 2 2 2)
      ((a^2 * ((Real.sin θ)^2 - (Real.cos θ)^2) * Sigma r a θ -
          2 * a^4 * (Real.cos θ)^2 * (Real.sin θ)^2) /
        (Sigma r a θ)^2) θ := by
  have hcs :=
    (Real.hasDerivAt_cos θ).mul (Real.hasDerivAt_sin θ)
  have hnum := hcs.const_mul (-a^2)
  have hreg := hnum.fun_div (Sigma_hasDerivAt_theta r a θ) hsig
  have hreg' :
      HasDerivAt
        (fun x : ℝ =>
          -a^2 * Real.cos x * Real.sin x / Sigma r a x)
        ((a^2 * ((Real.sin θ)^2 - (Real.cos θ)^2) * Sigma r a θ -
            2 * a^4 * (Real.cos θ)^2 * (Real.sin θ)^2) /
          (Sigma r a θ)^2) θ := by
    convert hreg using 1
    field_simp [hsig]
    ring
  have hS :=
    (Sigma_hasDerivAt_theta r a θ).continuousAt.eventually_ne hsig
  have heq :
      (fun x : ℝ => kerrChristoffel r M a Q x 2 2 2) =ᶠ[𝓝 θ]
        (fun x : ℝ =>
          -a^2 * Real.cos x * Real.sin x / Sigma r a x) := by
    filter_upwards [hS] with x hxS
    exact kerrChristoffel_theta_thetatheta r M a Q x hxS hdel
  exact hreg'.congr_of_eventuallyEq heq

/-- Polar derivative of the polar connection trace. -/
theorem kerrChristoffelTrace_theta_hasDerivAt_theta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => kerrChristoffelTrace r M a Q x 2)
      (-1 / (Real.sin θ)^2 +
        (2 * a^2 * ((Real.sin θ)^2 - (Real.cos θ)^2) * Sigma r a θ -
          4 * a^4 * (Real.cos θ)^2 * (Real.sin θ)^2) /
            (Sigma r a θ)^2) θ := by
  have hcot :=
    (Real.hasDerivAt_cos θ).fun_div (Real.hasDerivAt_sin θ) hsin
  have hcs :=
    (Real.hasDerivAt_cos θ).mul (Real.hasDerivAt_sin θ)
  have hnum := hcs.const_mul (-2 * a^2)
  have hfrac := hnum.fun_div (Sigma_hasDerivAt_theta r a θ) hsig
  have hreg := hcot.add hfrac
  have hreg' :
      HasDerivAt
        (fun x : ℝ =>
          Real.cos x / Real.sin x -
            2 * a^2 * Real.cos x * Real.sin x / Sigma r a x)
        (-1 / (Real.sin θ)^2 +
          (2 * a^2 * ((Real.sin θ)^2 - (Real.cos θ)^2) * Sigma r a θ -
            4 * a^4 * (Real.cos θ)^2 * (Real.sin θ)^2) /
              (Sigma r a θ)^2) θ := by
    convert hreg using 1
    · ring
    · have htrig := Real.sin_sq_add_cos_sq θ
      field_simp [hsig, hsin]
      nlinarith
  have hS :=
    (Sigma_hasDerivAt_theta r a θ).continuousAt.eventually_ne hsig
  have hSin :=
    (Real.hasDerivAt_sin θ).continuousAt.eventually_ne hsin
  have heq :
      (fun x : ℝ => kerrChristoffelTrace r M a Q x 2) =ᶠ[𝓝 θ]
        (fun x : ℝ =>
          Real.cos x / Real.sin x -
            2 * a^2 * Real.cos x * Real.sin x / Sigma r a x) := by
    filter_upwards [hS, hSin] with x hxS hxSin
    exact kerrChristoffelTrace_theta r M a Q x hxS hdel hxSin
  exact hreg'.congr_of_eventuallyEq heq

theorem kerrChristoffelPartial_r_thetatheta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffelPartial 1 r M a Q θ 1 2 2 =
      ((-Delta r M a Q - 2 * r * (r - M)) * Sigma r a θ +
        2 * r^2 * Delta r M a Q) / (Sigma r a θ)^2 := by
  unfold kerrChristoffelPartial kerrCoordPartial
  simpa using
    (kerrChristoffel_r_thetatheta_hasDerivAt_r
      r M a Q θ hsig hdel).deriv

theorem kerrChristoffelPartial_theta_thetatheta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0) :
    kerrChristoffelPartial 2 r M a Q θ 2 2 2 =
      (a^2 * ((Real.sin θ)^2 - (Real.cos θ)^2) * Sigma r a θ -
        2 * a^4 * (Real.cos θ)^2 * (Real.sin θ)^2) /
          (Sigma r a θ)^2 := by
  unfold kerrChristoffelPartial kerrCoordPartial
  simpa using
    (kerrChristoffel_theta_thetatheta_hasDerivAt_theta
      r M a Q θ hsig hdel).deriv

theorem kerrChristoffelTracePartial_theta_theta
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrCoordPartial 2
      (fun rr th => kerrChristoffelTrace rr M a Q th 2)
      r θ =
      -1 / (Real.sin θ)^2 +
        (2 * a^2 * ((Real.sin θ)^2 - (Real.cos θ)^2) * Sigma r a θ -
          4 * a^4 * (Real.cos θ)^2 * (Real.sin θ)^2) /
            (Sigma r a θ)^2 := by
  unfold kerrCoordPartial
  simpa using
    (kerrChristoffelTrace_theta_hasDerivAt_theta
      r M a Q θ hsig hdel hsin).deriv

/-- Coordinate derivatives of odd-parity Christoffels vanish identically as well. -/
@[simp] theorem kerrChristoffelPartial_zero_of_odd_stationary
    (κ : Fin 4) (r M a Q θ : ℝ)
    (ρ μ ν : Fin 4)
    (hodd :
      kerrStationarySign ρ *
        kerrStationarySign μ *
        kerrStationarySign ν = -1) :
    kerrChristoffelPartial κ r M a Q θ ρ μ ν = 0 := by
  unfold kerrChristoffelPartial kerrCoordPartial
  by_cases h1 : κ = 1
  · rw [if_pos h1]
    have hfun :
        (fun x : ℝ =>
          kerrChristoffel x M a Q θ ρ μ ν) =
        (fun _ : ℝ => 0) := by
      funext x
      exact kerrChristoffel_zero_of_odd_stationary
        x M a Q θ ρ μ ν hodd
    rw [hfun]
    simp
  · rw [if_neg h1]
    by_cases h2 : κ = 2
    · rw [if_pos h2]
      have hfun :
          (fun x : ℝ =>
            kerrChristoffel r M a Q x ρ μ ν) =
          (fun _ : ℝ => 0) := by
        funext x
        exact kerrChristoffel_zero_of_odd_stationary
          r M a Q x ρ μ ν hodd
      rw [hfun]
      simp
    · rw [if_neg h2]

/-- Coordinate differentiation preserves the symmetry of the two lower Christoffel indices. -/
theorem kerrChristoffelPartial_lower_symmetric
    (κ : Fin 4) (r M a Q θ : ℝ)
    (ρ μ ν : Fin 4) :
    kerrChristoffelPartial κ r M a Q θ ρ μ ν =
      kerrChristoffelPartial κ r M a Q θ ρ ν μ := by
  unfold kerrChristoffelPartial kerrCoordPartial
  by_cases h1 : κ = 1
  · rw [if_pos h1]
    have hfun :
        (fun x : ℝ => kerrChristoffel x M a Q θ ρ μ ν) =
          (fun x : ℝ => kerrChristoffel x M a Q θ ρ ν μ) := by
      funext x
      exact kerrChristoffel_lower_symmetric x M a Q θ ρ μ ν
    rw [hfun]
  · rw [if_neg h1]
    by_cases h2 : κ = 2
    · rw [if_pos h2]
      have hfun :
          (fun x : ℝ => kerrChristoffel r M a Q x ρ μ ν) =
            (fun x : ℝ => kerrChristoffel r M a Q x ρ ν μ) := by
        funext x
        exact kerrChristoffel_lower_symmetric r M a Q x ρ μ ν
      rw [hfun]
    · rw [if_neg h2]


/-- The quadratic Ricci contraction is symmetric in its two free lower indices. -/
theorem kerrConnectionProductTrace_symmetric
    (r M a Q θ : ℝ) (μ ν : Fin 4) :
    kerrConnectionProductTrace r M a Q θ μ ν =
      kerrConnectionProductTrace r M a Q θ ν μ := by
  unfold kerrConnectionProductTrace
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro ρ hρ
  ring

/-- Ricci tensor obtained by contracting the standard coordinate Riemann formula. -/
def kerrRicciCovFromMetric
    (r M a Q θ : ℝ)
    (μ ν : Fin 4) : ℝ :=
  (∑ ρ : Fin 4,
    (kerrChristoffelPartial ρ r M a Q θ ρ μ ν +
     kerrChristoffel r M a Q θ ρ μ ν *
       kerrChristoffelTrace r M a Q θ ρ -
     ∑ σ : Fin 4,
       kerrChristoffel r M a Q θ σ μ ρ *
         kerrChristoffel r M a Q θ ρ ν σ)) -
  kerrCoordPartial ν
    (fun rr th => kerrChristoffelTrace rr M a Q th μ) r θ


/-- Equivalent contracted form with the quadratic connection trace pulled outside the
outer sum. -/
theorem kerrRicciCovFromMetric_contracted
    (r M a Q θ : ℝ) (μ ν : Fin 4) :
    kerrRicciCovFromMetric r M a Q θ μ ν =
      (∑ ρ : Fin 4,
        (kerrChristoffelPartial ρ r M a Q θ ρ μ ν +
         kerrChristoffel r M a Q θ ρ μ ν *
           kerrChristoffelTrace r M a Q θ ρ)) -
      kerrConnectionProductTrace r M a Q θ μ ν -
      kerrCoordPartial ν
        (fun rr th => kerrChristoffelTrace rr M a Q th μ) r θ := by
  unfold kerrRicciCovFromMetric kerrConnectionProductTrace
  rw [Finset.sum_sub_distrib]

/-- The stationary off-diagonal Ricci component is symmetric without any curvature
component evaluation: stationarity kills the trace derivatives and all remaining
terms are symmetric algebraically. -/
theorem kerrRicci_tphi_symmetric
    (r M a Q θ : ℝ) :
    kerrRicciCovFromMetric r M a Q θ 0 3 =
      kerrRicciCovFromMetric r M a Q θ 3 0 := by
  rw [kerrRicciCovFromMetric_contracted,
      kerrRicciCovFromMetric_contracted]
  have hsum :
      (∑ ρ : Fin 4,
        (kerrChristoffelPartial ρ r M a Q θ ρ 0 3 +
         kerrChristoffel r M a Q θ ρ 0 3 *
           kerrChristoffelTrace r M a Q θ ρ)) =
      (∑ ρ : Fin 4,
        (kerrChristoffelPartial ρ r M a Q θ ρ 3 0 +
         kerrChristoffel r M a Q θ ρ 3 0 *
           kerrChristoffelTrace r M a Q θ ρ)) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [kerrChristoffelPartial_lower_symmetric
          ρ r M a Q θ ρ 0 3,
        kerrChristoffel_lower_symmetric
          r M a Q θ ρ 0 3]
  rw [hsum, kerrConnectionProductTrace_symmetric
      r M a Q θ 0 3]
  simp [kerrCoordPartial]

/-- The metric-derived Ricci tensor inherits stationary-reflection parity. -/
theorem kerrRicciCovFromMetric_stationary_parity
    (r M a Q θ : ℝ)
    (μ ν : Fin 4) :
    kerrStationarySign μ *
        kerrStationarySign ν *
        kerrRicciCovFromMetric r M a Q θ μ ν =
      kerrRicciCovFromMetric r M a Q θ μ ν := by
  fin_cases μ <;> fin_cases ν <;>
    simp [kerrStationarySign, kerrRicciCovFromMetric,
      kerrChristoffel_zero_of_odd_stationary] <;> ring

/-- Therefore every stationary-meridional Ricci cross component vanishes identically. -/
theorem kerrRicciCovFromMetric_zero_of_odd_stationary
    (r M a Q θ : ℝ)
    (μ ν : Fin 4)
    (hodd :
      kerrStationarySign μ *
        kerrStationarySign ν = -1) :
    kerrRicciCovFromMetric r M a Q θ μ ν = 0 := by
  have hp :=
    kerrRicciCovFromMetric_stationary_parity
      r M a Q θ μ ν
  rw [hodd] at hp
  linarith

/-! ### Stationary-block Ricci reduction -/

/-- Every stationary-block Ricci component has the same two-dimensional divergence
form because t and phi derivatives vanish identically. -/
theorem kerrRicci_stationary_reduction
    (r M a Q θ : ℝ) (A B : Fin 4)
    (hA : A = 0 ∨ A = 3) (hB : B = 0 ∨ B = 3) :
    kerrRicciCovFromMetric r M a Q θ A B =
      kerrChristoffelPartial 1 r M a Q θ 1 A B +
      kerrChristoffelPartial 2 r M a Q θ 2 A B +
      kerrChristoffel r M a Q θ 1 A B *
        kerrChristoffelTrace r M a Q θ 1 +
      kerrChristoffel r M a Q θ 2 A B *
        kerrChristoffelTrace r M a Q θ 2 -
      kerrConnectionProductTrace r M a Q θ A B := by
  rcases hA with rfl | rfl <;>
    rcases hB with rfl | rfl <;>
    unfold kerrRicciCovFromMetric kerrConnectionProductTrace <;>
    simp [kerrCoordPartial, kerrStationarySign,
      kerrChristoffel_zero_of_odd_stationary] <;> ring

/-- The final stationary Ricci component is algebraically tied to the already-closed
t-phi component by the square-form metric. -/
theorem kerrRicci_phiphi_plus_scaled_tphi
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrRicciCovFromMetric r M a Q θ 3 3 +
        a * (Real.sin θ)^2 *
          kerrRicciCovFromMetric r M a Q θ 0 3 =
      Q^2 * (Real.sin θ)^2 * (r^2 + a^2) / (Sigma r a θ)^2 := by
  rw [kerrRicci_stationary_reduction r M a Q θ 3 3
        (Or.inr rfl) (Or.inr rfl),
      kerrRicci_stationary_reduction r M a Q θ 0 3
        (Or.inl rfl) (Or.inr rfl),
      kerrChristoffelPartial_r_phiphi_relation r M a Q θ hsig hdel,
      kerrChristoffelPartial_theta_phiphi_relation r M a Q θ hsig hdel,
      kerrChristoffel_r_phiphi_relation r M a Q θ hsig hdel,
      kerrChristoffel_theta_phiphi_relation r M a Q θ hsig hdel,
      kerrChristoffelPartial_r_tphi r M a Q θ hsig hdel,
      kerrChristoffelPartial_theta_tphi r M a Q θ hsig hdel,
      kerrChristoffel_theta_tphi r M a Q θ hsig hdel,
      kerrChristoffelTrace_r r M a Q θ hsig hdel hsin,
      kerrChristoffelTrace_theta r M a Q θ hsig hdel hsin,
      kerrConnectionProductTrace_phiphi_tphi_relation
        r M a Q θ hsig hdel hsin]
  unfold kerrPhiPhiRadialRemainder kerrPhiPhiPolarRemainder
    kerrConnectionProductTracePhiCorrectionNumerator kerrStationaryA kerrH
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma
  nlinarith

theorem kerrRicci_tphi_reduction
    (r M a Q θ : ℝ) :
    kerrRicciCovFromMetric r M a Q θ 0 3 =
      kerrChristoffelPartial 1 r M a Q θ 1 0 3 +
      kerrChristoffelPartial 2 r M a Q θ 2 0 3 +
      kerrChristoffel r M a Q θ 1 0 3 *
        kerrChristoffelTrace r M a Q θ 1 +
      kerrChristoffel r M a Q θ 2 0 3 *
        kerrChristoffelTrace r M a Q θ 2 -
      kerrConnectionProductTrace r M a Q θ 0 3 := by
  exact kerrRicci_stationary_reduction r M a Q θ 0 3
    (Or.inl rfl) (Or.inr rfl)

theorem kerrRicci_tt_reduction
    (r M a Q θ : ℝ) :
    kerrRicciCovFromMetric r M a Q θ 0 0 =
      kerrChristoffelPartial 1 r M a Q θ 1 0 0 +
      kerrChristoffelPartial 2 r M a Q θ 2 0 0 +
      kerrChristoffel r M a Q θ 1 0 0 *
        kerrChristoffelTrace r M a Q θ 1 +
      kerrChristoffel r M a Q θ 2 0 0 *
        kerrChristoffelTrace r M a Q θ 2 -
      kerrConnectionProductTrace r M a Q θ 0 0 := by
  exact kerrRicci_stationary_reduction r M a Q θ 0 0
    (Or.inl rfl) (Or.inl rfl)

/-! ### Radial diagonal Ricci equation -/

theorem kerrRicci_rr_reduction
    (r M a Q θ : ℝ) :
    kerrRicciCovFromMetric r M a Q θ 1 1 =
      kerrChristoffelPartial 1 r M a Q θ 1 1 1 +
      kerrChristoffelPartial 2 r M a Q θ 2 1 1 -
      kerrCoordPartial 1
        (fun rr th => kerrChristoffelTrace rr M a Q th 1) r θ +
      kerrChristoffel r M a Q θ 1 1 1 *
        kerrChristoffelTrace r M a Q θ 1 +
      kerrChristoffel r M a Q θ 2 1 1 *
        kerrChristoffelTrace r M a Q θ 2 -
      kerrConnectionProductTrace r M a Q θ 1 1 := by
  unfold kerrRicciCovFromMetric kerrConnectionProductTrace
  simp [kerrStationarySign,
    kerrChristoffel_zero_of_odd_stationary, kerrCoordPartial]
  ring

/-! ### Polar diagonal Ricci equation -/

/-- Structural reduction of the polar diagonal Ricci component to two explicit
connection derivatives, the polar trace derivative, and the quadratic contraction. -/
theorem kerrRicci_thetatheta_reduction
    (r M a Q θ : ℝ) :
    kerrRicciCovFromMetric r M a Q θ 2 2 =
      kerrChristoffelPartial 1 r M a Q θ 1 2 2 +
      kerrChristoffelPartial 2 r M a Q θ 2 2 2 -
      kerrCoordPartial 2
        (fun rr th => kerrChristoffelTrace rr M a Q th 2) r θ +
      kerrChristoffel r M a Q θ 1 2 2 *
        kerrChristoffelTrace r M a Q θ 1 +
      kerrChristoffel r M a Q θ 2 2 2 *
        kerrChristoffelTrace r M a Q θ 2 -
      kerrConnectionProductTrace r M a Q θ 2 2 := by
  unfold kerrRicciCovFromMetric kerrConnectionProductTrace
  simp [kerrStationarySign,
    kerrChristoffel_zero_of_odd_stationary, kerrCoordPartial]
  ring

/-! ### Mixed meridional Ricci equation -/

/-- Structural reduction of `R_{rθ}` to the two meridional Christoffels, the two
connection traces, and the cross-connection contraction. -/
theorem kerrRicci_rtheta_reduction
    (r M a Q θ : ℝ) :
    kerrRicciCovFromMetric r M a Q θ 1 2 =
      kerrChristoffelPartial 1 r M a Q θ 1 1 2 +
      kerrChristoffelPartial 2 r M a Q θ 2 1 2 -
      kerrCoordPartial 2
        (fun rr th => kerrChristoffelTrace rr M a Q th 1)
        r θ +
      kerrChristoffel r M a Q θ 1 1 2 *
        kerrChristoffelTrace r M a Q θ 1 +
      kerrChristoffel r M a Q θ 2 1 2 *
        kerrChristoffelTrace r M a Q θ 2 -
      kerrConnectionCrossTrace r M a Q θ := by
  unfold kerrRicciCovFromMetric kerrConnectionCrossTrace
  simp [kerrStationarySign,
    kerrChristoffel_zero_of_odd_stationary]
  ring

/-- The Kerr-Newman metric has identically vanishing mixed meridional Ricci component. -/
theorem kerrRicci_rtheta_zero
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrRicciCovFromMetric r M a Q θ 1 2 = 0 := by
  rw [kerrRicci_rtheta_reduction,
    kerrChristoffelPartial_r_rtheta r M a Q θ hsig hdel,
    kerrChristoffelPartial_theta_rtheta r M a Q θ hsig hdel,
    kerrChristoffelTracePartial_theta_r r M a Q θ hsig hdel hsin,
    kerrChristoffel_r_rtheta r M a Q θ hsig hdel,
    kerrChristoffel_theta_rtheta r M a Q θ hsig hdel,
    kerrChristoffelTrace_r r M a Q θ hsig hdel hsin,
    kerrChristoffelTrace_theta r M a Q θ hsig hdel hsin,
    kerrConnectionCrossTrace_formula r M a Q θ hsig hdel hsin]
  field_simp [hsig, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Sigma
  nlinarith

/-- Reverse-order mixed meridional Ricci component has the analogous reduction. -/
theorem kerrRicci_thetar_reduction
    (r M a Q θ : ℝ) :
    kerrRicciCovFromMetric r M a Q θ 2 1 =
      kerrChristoffelPartial 1 r M a Q θ 1 1 2 +
      kerrChristoffelPartial 2 r M a Q θ 2 1 2 -
      kerrCoordPartial 1
        (fun rr th => kerrChristoffelTrace rr M a Q th 2)
        r θ +
      kerrChristoffel r M a Q θ 1 1 2 *
        kerrChristoffelTrace r M a Q θ 1 +
      kerrChristoffel r M a Q θ 2 1 2 *
        kerrChristoffelTrace r M a Q θ 2 -
      kerrConnectionCrossTrace r M a Q θ := by
  rw [kerrChristoffel_lower_symmetric r M a Q θ 1 2 1,
      kerrChristoffel_lower_symmetric r M a Q θ 2 2 1]
  unfold kerrRicciCovFromMetric kerrConnectionCrossTrace
  simp [kerrStationarySign,
    kerrChristoffel_zero_of_odd_stationary]
  ring

/-- The reverse mixed meridional Ricci component also vanishes directly. -/
theorem kerrRicci_thetar_zero
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrRicciCovFromMetric r M a Q θ 2 1 = 0 := by
  rw [kerrRicci_thetar_reduction,
    kerrChristoffelPartial_r_rtheta r M a Q θ hsig hdel,
    kerrChristoffelPartial_theta_rtheta r M a Q θ hsig hdel,
    kerrChristoffelTracePartial_r_theta r M a Q θ hsig hdel hsin,
    kerrChristoffel_r_rtheta r M a Q θ hsig hdel,
    kerrChristoffel_theta_rtheta r M a Q θ hsig hdel,
    kerrChristoffelTrace_r r M a Q θ hsig hdel hsin,
    kerrChristoffelTrace_theta r M a Q θ hsig hdel hsin,
    kerrConnectionCrossTrace_formula r M a Q θ hsig hdel hsin]
  field_simp [hsig, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Sigma
  nlinarith

/-! ### Einstein equations already closed by stationary-reflection parity -/

/-- All ordered stationary-meridional Ricci components vanish identically. -/
theorem kerrRicci_stationary_meridional_zero
    (r M a Q θ : ℝ) :
    kerrRicciCovFromMetric r M a Q θ 0 1 = 0 ∧
    kerrRicciCovFromMetric r M a Q θ 0 2 = 0 ∧
    kerrRicciCovFromMetric r M a Q θ 3 1 = 0 ∧
    kerrRicciCovFromMetric r M a Q θ 3 2 = 0 ∧
    kerrRicciCovFromMetric r M a Q θ 1 0 = 0 ∧
    kerrRicciCovFromMetric r M a Q θ 2 0 = 0 ∧
    kerrRicciCovFromMetric r M a Q θ 1 3 = 0 ∧
    kerrRicciCovFromMetric r M a Q θ 2 3 = 0 := by
  constructor
  · apply kerrRicciCovFromMetric_zero_of_odd_stationary
    norm_num [kerrStationarySign]
  · constructor
    · apply kerrRicciCovFromMetric_zero_of_odd_stationary
      norm_num [kerrStationarySign]
    · constructor
      · apply kerrRicciCovFromMetric_zero_of_odd_stationary
        norm_num [kerrStationarySign]
      · constructor
        · apply kerrRicciCovFromMetric_zero_of_odd_stationary
          norm_num [kerrStationarySign]
        · constructor
          · apply kerrRicciCovFromMetric_zero_of_odd_stationary
            norm_num [kerrStationarySign]
          · constructor
            · apply kerrRicciCovFromMetric_zero_of_odd_stationary
              norm_num [kerrStationarySign]
            · constructor
              · apply kerrRicciCovFromMetric_zero_of_odd_stationary
                norm_num [kerrStationarySign]
              · apply kerrRicciCovFromMetric_zero_of_odd_stationary
                norm_num [kerrStationarySign]

/-- Scalar curvature computed from the metric-derived Ricci tensor. -/
def kerrScalarCurvatureFromMetric
    (r M a Q θ : ℝ) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4,
    kerrMetricInv r M a Q θ μ ν *
      kerrRicciCovFromMetric r M a Q θ μ ν

/-- Einstein tensor computed entirely from the Boyer-Lindquist metric. -/
def kerrEinsteinCovFromMetric
    (r M a Q θ : ℝ)
    (μ ν : Fin 4) : ℝ :=
  kerrRicciCovFromMetric r M a Q θ μ ν -
    (1 / 2 : ℝ) *
      kerrMetricCov r M a Q θ μ ν *
      kerrScalarCurvatureFromMetric r M a Q θ

/-! ### Full coordinate-to-Carter-coframe Maxwell specialization -/

/-- Embed a stationary `(dt,dφ)` covector into Boyer-Lindquist
`(dt,dr,dθ,dφ)` components. -/
def stationaryCovectorLift (α : R2) : Fin 4 → ℝ :=
  fun i =>
    if i = 0 then α.1
    else if i = 3 then α.2
    else 0

/-- Coordinate wedge of two covectors. -/
def covectorWedge4
    (α β : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  α i * β j - α j * β i

theorem covectorWedge4_smul_smul
    (c d : ℝ) (α β : Fin 4 → ℝ) (i j : Fin 4) :
    covectorWedge4 (c • α) (d • β) i j =
      (c * d) * covectorWedge4 α β i j := by
  simp [covectorWedge4]
  ring

/-- Carter orthonormal temporal coframe leg in Boyer-Lindquist components. -/
def kerrCoframe0
    (r M a Q θ : ℝ) : Fin 4 → ℝ :=
  (Delta r M a Q /
      Real.sqrt (Sigma r a θ * Delta r M a Q)) •
    stationaryCovectorLift (kerrTemporalOneFormCoeffs a θ)

/-- Carter orthonormal radial coframe leg. -/
def kerrCoframe1
    (r M a Q θ : ℝ) : Fin 4 → ℝ :=
  (Real.sqrt (Sigma r a θ * Delta r M a Q) /
      Delta r M a Q) • principalBasis 1

/-- Carter orthonormal polar coframe leg. -/
def kerrCoframe2
    (r a θ : ℝ) : Fin 4 → ℝ :=
  Real.sqrt (Sigma r a θ) • principalBasis 2

/-- Carter orthonormal azimuthal coframe leg. -/
def kerrCoframe3
    (r a θ : ℝ) : Fin 4 → ℝ :=
  (Real.sin θ / Real.sqrt (Sigma r a θ)) •
    stationaryCovectorLift (kerrAxialOneFormCoeffs r a)


/-! ### Carter coframe orthonormality from the certified inverse metric -/

/-- Inverse-metric pairing of coordinate covectors. -/
def kerrCovectorInner
    (r M a Q θ : ℝ)
    (α β : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    kerrMetricInv r M a Q θ i j * α i * β j

/-- The temporal Carter coframe leg has norm minus one. -/
theorem kerrCoframe0_norm
    (r M a Q θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (hsin : Real.sin θ ≠ 0) :
    kerrCovectorInner r M a Q θ
      (kerrCoframe0 r M a Q θ)
      (kerrCoframe0 r M a Q θ) = -1 := by
  have hsig0 : Sigma r a θ ≠ 0 := ne_of_gt hsig
  have hdel0 : Delta r M a Q ≠ 0 := ne_of_gt hdel
  have hSD : 0 < Sigma r a θ * Delta r M a Q := mul_pos hsig hdel
  have hsqrt0 :
      Real.sqrt (Sigma r a θ * Delta r M a Q) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hSD)
  have hsqrt2 :
      (Real.sqrt (Sigma r a θ * Delta r M a Q))^2 =
        Sigma r a θ * Delta r M a Q :=
    Real.sq_sqrt (le_of_lt hSD)
  unfold kerrCovectorInner kerrCoframe0 stationaryCovectorLift
  simp [kerrMetricInv, kerrTemporalOneFormCoeffs]
  have htrig :
      (Real.sin θ)^2 = 1 - (Real.cos θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [htrig]
  field_simp [hsig0, hdel0, hsqrt0]
  unfold Sigma
  nlinarith

/-- The radial Carter coframe leg has norm plus one. -/
theorem kerrCoframe1_norm
    (r M a Q θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q) :
    kerrCovectorInner r M a Q θ
      (kerrCoframe1 r M a Q θ)
      (kerrCoframe1 r M a Q θ) = 1 := by
  have hsig0 : Sigma r a θ ≠ 0 := ne_of_gt hsig
  have hdel0 : Delta r M a Q ≠ 0 := ne_of_gt hdel
  have hSD : 0 < Sigma r a θ * Delta r M a Q := mul_pos hsig hdel
  have hsqrt2 :
      (Real.sqrt (Sigma r a θ * Delta r M a Q))^2 =
        Sigma r a θ * Delta r M a Q :=
    Real.sq_sqrt (le_of_lt hSD)
  unfold kerrCovectorInner kerrCoframe1
  simp [kerrMetricInv, principalBasis]
  field_simp [hsig0, hdel0]
  nlinarith

/-- The polar Carter coframe leg has norm plus one. -/
theorem kerrCoframe2_norm
    (r M a Q θ : ℝ)
    (hsig : 0 < Sigma r a θ) :
    kerrCovectorInner r M a Q θ
      (kerrCoframe2 r a θ)
      (kerrCoframe2 r a θ) = 1 := by
  have hsig0 : Sigma r a θ ≠ 0 := ne_of_gt hsig
  have hsqrt2 :
      (Real.sqrt (Sigma r a θ))^2 =
        Sigma r a θ :=
    Real.sq_sqrt (le_of_lt hsig)
  unfold kerrCovectorInner kerrCoframe2
  simp [kerrMetricInv, principalBasis]
  field_simp [hsig0]
  nlinarith

/-- The azimuthal Carter coframe leg has norm plus one. -/
theorem kerrCoframe3_norm
    (r M a Q θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (hsin : Real.sin θ ≠ 0) :
    kerrCovectorInner r M a Q θ
      (kerrCoframe3 r a θ)
      (kerrCoframe3 r a θ) = 1 := by
  have hsig0 : Sigma r a θ ≠ 0 := ne_of_gt hsig
  have hdel0 : Delta r M a Q ≠ 0 := ne_of_gt hdel
  have hsqrt0 : Real.sqrt (Sigma r a θ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hsig)
  have hsqrt2 :
      (Real.sqrt (Sigma r a θ))^2 =
        Sigma r a θ :=
    Real.sq_sqrt (le_of_lt hsig)
  unfold kerrCovectorInner kerrCoframe3 stationaryCovectorLift
  simp [kerrMetricInv, kerrAxialOneFormCoeffs]
  have htrig :
      (Real.sin θ)^2 = 1 - (Real.cos θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [htrig]
  field_simp [hsig0, hdel0, hsin, hsqrt0]
  unfold Sigma
  nlinarith

/-- Temporal and azimuthal stationary coframe legs are orthogonal. -/
theorem kerrCoframe0_orthogonal_3
    (r M a Q θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (hsin : Real.sin θ ≠ 0) :
    kerrCovectorInner r M a Q θ
      (kerrCoframe0 r M a Q θ)
      (kerrCoframe3 r a θ) = 0 := by
  have hsig0 : Sigma r a θ ≠ 0 := ne_of_gt hsig
  have hdel0 : Delta r M a Q ≠ 0 := ne_of_gt hdel
  have hS0 : Real.sqrt (Sigma r a θ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hsig)
  have hSD : 0 < Sigma r a θ * Delta r M a Q := mul_pos hsig hdel
  have hSD0 :
      Real.sqrt (Sigma r a θ * Delta r M a Q) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hSD)
  unfold kerrCovectorInner kerrCoframe0 kerrCoframe3
    stationaryCovectorLift
  simp [kerrMetricInv, kerrTemporalOneFormCoeffs,
    kerrAxialOneFormCoeffs]
  have htrig :
      (Real.sin θ)^2 = 1 - (Real.cos θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [htrig]
  field_simp [hsig0, hdel0, hsin, hS0, hSD0]
  unfold Sigma
  ring

/-- Radial and polar legs are orthogonal to each other and to the stationary block
because the Boyer-Lindquist inverse metric is block diagonal. -/
theorem kerrCoframe_nonstationary_orthogonality
    (r M a Q θ : ℝ) :
    kerrCovectorInner r M a Q θ
      (kerrCoframe1 r M a Q θ)
      (kerrCoframe2 r a θ) = 0 ∧
    kerrCovectorInner r M a Q θ
      (kerrCoframe0 r M a Q θ)
      (kerrCoframe1 r M a Q θ) = 0 ∧
    kerrCovectorInner r M a Q θ
      (kerrCoframe0 r M a Q θ)
      (kerrCoframe2 r a θ) = 0 ∧
    kerrCovectorInner r M a Q θ
      (kerrCoframe3 r a θ)
      (kerrCoframe1 r M a Q θ) = 0 ∧
    kerrCovectorInner r M a Q θ
      (kerrCoframe3 r a θ)
      (kerrCoframe2 r a θ) = 0 := by
  unfold kerrCovectorInner kerrCoframe0 kerrCoframe1
    kerrCoframe2 kerrCoframe3 stationaryCovectorLift
  simp [kerrMetricInv, principalBasis]

/-- Bundle the four Carter legs into one indexed coframe. -/
def kerrCoframe
    (r M a Q θ : ℝ) (A : Fin 4) : Fin 4 → ℝ :=
  if A = 0 then kerrCoframe0 r M a Q θ
  else if A = 1 then kerrCoframe1 r M a Q θ
  else if A = 2 then kerrCoframe2 r a θ
  else kerrCoframe3 r a θ

/-- The Carter coframe is genuinely orthonormal for the certified inverse metric. -/
theorem kerrCoframe_orthonormal
    (r M a Q θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (hsin : Real.sin θ ≠ 0)
    (A B : Fin 4) :
    kerrCovectorInner r M a Q θ
      (kerrCoframe r M a Q θ A)
      (kerrCoframe r M a Q θ B) =
      (if A = B then principalMetricSign A else 0) := by
  rcases kerrCoframe_nonstationary_orthogonality
    r M a Q θ with
    ⟨h12, h01, h02, h31, h32⟩
  have h03 :=
    kerrCoframe0_orthogonal_3 r M a Q θ
      hsig hdel hsin
  have h10 :
      kerrCovectorInner r M a Q θ
        (kerrCoframe1 r M a Q θ)
        (kerrCoframe0 r M a Q θ) = 0 := by
    unfold kerrCovectorInner at h01 ⊢
    simpa [mul_comm] using h01
  have h20 :
      kerrCovectorInner r M a Q θ
        (kerrCoframe2 r a θ)
        (kerrCoframe0 r M a Q θ) = 0 := by
    unfold kerrCovectorInner at h02 ⊢
    simpa [mul_comm] using h02
  have h13 :
      kerrCovectorInner r M a Q θ
        (kerrCoframe1 r M a Q θ)
        (kerrCoframe3 r a θ) = 0 := by
    unfold kerrCovectorInner at h31 ⊢
    simpa [mul_comm] using h31
  have h23 :
      kerrCovectorInner r M a Q θ
        (kerrCoframe2 r a θ)
        (kerrCoframe3 r a θ) = 0 := by
    unfold kerrCovectorInner at h32 ⊢
    simpa [mul_comm] using h32
  have h30 :
      kerrCovectorInner r M a Q θ
        (kerrCoframe3 r a θ)
        (kerrCoframe0 r M a Q θ) = 0 := by
    unfold kerrCovectorInner at h03 ⊢
    simpa [mul_comm] using h03
  have h21 :
      kerrCovectorInner r M a Q θ
        (kerrCoframe2 r a θ)
        (kerrCoframe1 r M a Q θ) = 0 := by
    unfold kerrCovectorInner at h12 ⊢
    simpa [mul_comm] using h12
  fin_cases A <;> fin_cases B <;>
    simp [kerrCoframe, principalMetricSign,
      kerrCoframe0_norm r M a Q θ hsig hdel hsin,
      kerrCoframe1_norm r M a Q θ hsig hdel,
      kerrCoframe2_norm r M a Q θ hsig,
      kerrCoframe3_norm r M a Q θ hsig hdel hsin,
      h03, h30, h01, h10, h02, h20,
      h31, h13, h32, h23, h12, h21]


/-! ### Einstein-equation Ricci target selected by the Maxwell field and Carter coframe -/

/-- Electrovac Ricci eigenvalue scale forced by the principal Maxwell field. -/
def kerrRicciScale (Q r a θ : ℝ) : ℝ :=
  Q^2 / (Sigma r a θ)^2

/-- Covariant Ricci coefficients in the orthonormal Carter frame:
diag(q,-q,q,q). -/
def kerrRicciFrameCovCoeff
    (Q r a θ : ℝ) (A : Fin 4) : ℝ :=
  if A = 0 then kerrRicciScale Q r a θ
  else if A = 1 then -kerrRicciScale Q r a θ
  else kerrRicciScale Q r a θ

/-- Coordinate covariant tensor forced by the Einstein-Maxwell equation once expressed in
the metric-selected Carter coframe. -/
def kerrEinsteinTargetRicciCov
    (Q r M a θ : ℝ) (i j : Fin 4) : ℝ :=
  ∑ A : Fin 4,
    kerrRicciFrameCovCoeff Q r a θ A *
      kerrCoframe r M a Q θ A i *
      kerrCoframe r M a Q θ A j

/-- Explicit Boyer-Lindquist components of the field-forced Ricci target. -/
def kerrEinsteinTargetRicciCoordinate
    (Q r M a θ : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then
    kerrRicciScale Q r a θ *
      (Delta r M a Q + a^2 * (Real.sin θ)^2) /
      Sigma r a θ
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
    -kerrRicciScale Q r a θ * a * (Real.sin θ)^2 *
      (Delta r M a Q + (r^2 + a^2)) /
      Sigma r a θ
  else if i = 1 ∧ j = 1 then
    -kerrRicciScale Q r a θ *
      Sigma r a θ / Delta r M a Q
  else if i = 2 ∧ j = 2 then
    kerrRicciScale Q r a θ * Sigma r a θ
  else if i = 3 ∧ j = 3 then
    kerrRicciScale Q r a θ * (Real.sin θ)^2 *
      (a^2 * Delta r M a Q * (Real.sin θ)^2 +
        (r^2 + a^2)^2) /
      Sigma r a θ
  else 0


/-- The t-phi Ricci component is derived directly from the metric and equals the
Maxwell-forced Einstein target. -/
theorem kerrRicci_tphi_eq_target
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrRicciCovFromMetric r M a Q θ 0 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 3 := by
  rw [kerrRicci_tphi_reduction,
    kerrChristoffelPartial_r_tphi r M a Q θ hsig hdel,
    kerrChristoffelPartial_theta_tphi r M a Q θ hsig hdel,
    kerrChristoffel_r_tphi r M a Q θ hsig hdel,
    kerrChristoffel_theta_tphi r M a Q θ hsig hdel,
    kerrChristoffelTrace_r r M a Q θ hsig hdel hsin,
    kerrChristoffelTrace_theta r M a Q θ hsig hdel hsin,
    kerrConnectionProductTrace_tphi_formula r M a Q θ hsig hdel hsin]
  simp [kerrEinsteinTargetRicciCoordinate, kerrRicciScale]
  unfold kerrConnectionProductTraceTPhiNumerator kerrStationaryA kerrH
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma
  nlinarith

/-- The last Kerr-Newman Ricci component is forced by the square-form relation and the
already-derived t-phi equation. -/
theorem kerrRicci_phiphi_eq_target
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrRicciCovFromMetric r M a Q θ 3 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 3 3 := by
  have hrel := kerrRicci_phiphi_plus_scaled_tphi
    r M a Q θ hsig hdel hsin
  rw [kerrRicci_tphi_eq_target Q r M a θ hsig hdel hsin] at hrel
  simp [kerrEinsteinTargetRicciCoordinate, kerrRicciScale] at hrel ⊢
  field_simp [hsig] at hrel ⊢
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma at hrel ⊢
  nlinarith

/-- The tt Ricci component is derived directly from the Boyer-Lindquist metric and
equals the Maxwell-forced target. -/
theorem kerrRicci_tt_eq_target
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrRicciCovFromMetric r M a Q θ 0 0 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 0 := by
  rw [kerrRicci_tt_reduction,
    kerrChristoffelPartial_r_tt r M a Q θ hsig hdel,
    kerrChristoffelPartial_theta_tt r M a Q θ hsig hdel,
    kerrChristoffel_r_tt r M a Q θ hsig hdel,
    kerrChristoffel_theta_tt r M a Q θ hsig hdel,
    kerrChristoffelTrace_r r M a Q θ hsig hdel hsin,
    kerrChristoffelTrace_theta r M a Q θ hsig hdel hsin,
    kerrConnectionProductTrace_tt_formula r M a Q θ hsig hdel hsin]
  simp [kerrEinsteinTargetRicciCoordinate, kerrRicciScale]
  unfold kerrStationaryA kerrH
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma
  nlinarith

/-- The radial diagonal Ricci tensor is derived from the metric and equals the
Maxwell-forced Einstein target. -/
theorem kerrRicci_rr_eq_target
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrRicciCovFromMetric r M a Q θ 1 1 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 1 1 := by
  rw [kerrRicci_rr_reduction,
    kerrChristoffelPartial_r_rr r M a Q θ hsig hdel,
    kerrChristoffelPartial_theta_rr r M a Q θ hsig hdel,
    kerrChristoffelTracePartial_r_r r M a Q θ hsig hdel hsin,
    kerrChristoffel_r_rr r M a Q θ hsig hdel,
    kerrChristoffel_theta_rr r M a Q θ hsig hdel,
    kerrChristoffelTrace_r r M a Q θ hsig hdel hsin,
    kerrChristoffelTrace_theta r M a Q θ hsig hdel hsin,
    kerrConnectionProductTrace_rr_formula r M a Q θ hsig hdel hsin]
  simp [kerrEinsteinTargetRicciCoordinate, kerrRicciScale]
  unfold kerrConnectionProductTraceRRNumerator
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma
  nlinarith

/-- The polar diagonal Ricci tensor is derived from the Boyer-Lindquist metric and equals
the Maxwell-forced Einstein target, with no imported curvature scalar. -/
theorem kerrRicci_thetatheta_eq_target
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrRicciCovFromMetric r M a Q θ 2 2 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 2 2 := by
  rw [kerrRicci_thetatheta_reduction,
    kerrChristoffelPartial_r_thetatheta r M a Q θ hsig hdel,
    kerrChristoffelPartial_theta_thetatheta r M a Q θ hsig hdel,
    kerrChristoffelTracePartial_theta_theta
      r M a Q θ hsig hdel hsin,
    kerrChristoffel_r_thetatheta r M a Q θ hsig hdel,
    kerrChristoffel_theta_thetatheta r M a Q θ hsig hdel,
    kerrChristoffelTrace_r r M a Q θ hsig hdel hsin,
    kerrChristoffelTrace_theta r M a Q θ hsig hdel hsin,
    kerrConnectionProductTrace_thetatheta_formula
      r M a Q θ hsig hdel hsin]
  simp [kerrEinsteinTargetRicciCoordinate, kerrRicciScale]
  field_simp [hsig, hdel, hsin]
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold Delta Sigma
  nlinarith

/-- This closes the `rθ` Einstein-Maxwell component because the field-forced target is zero. -/
theorem kerrRicci_rtheta_eq_target
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrRicciCovFromMetric r M a Q θ 1 2 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 1 2 := by
  rw [kerrRicci_rtheta_zero r M a Q θ hsig hdel hsin]
  simp [kerrEinsteinTargetRicciCoordinate]

theorem kerrRicci_thetar_eq_target
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrRicciCovFromMetric r M a Q θ 2 1 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 2 1 := by
  rw [kerrRicci_thetar_zero r M a Q θ hsig hdel hsin]
  simp [kerrEinsteinTargetRicciCoordinate]


/-- The explicit coordinate Einstein-Maxwell Ricci target is symmetric. -/
theorem kerrEinsteinTargetRicciCoordinate_symmetric
    (Q r M a θ : ℝ) (i j : Fin 4) :
    kerrEinsteinTargetRicciCoordinate Q r M a θ i j =
      kerrEinsteinTargetRicciCoordinate Q r M a θ j i := by
  fin_cases i <;> fin_cases j <;>
    simp [kerrEinsteinTargetRicciCoordinate]

/-- The explicit Einstein-Maxwell Ricci target has the same stationary-reflection parity
as any covariant rank-two tensor built from the Kerr-Newman geometry. -/
theorem kerrEinsteinTargetRicciCoordinate_stationary_parity
    (Q r M a θ : ℝ)
    (i j : Fin 4) :
    kerrStationarySign i * kerrStationarySign j *
        kerrEinsteinTargetRicciCoordinate Q r M a θ i j =
      kerrEinsteinTargetRicciCoordinate Q r M a θ i j := by
  fin_cases i <;> fin_cases j <;>
    simp [kerrStationarySign, kerrEinsteinTargetRicciCoordinate] <;> ring

/-- Every odd stationary-parity component of the field-forced Ricci target vanishes. -/
theorem kerrEinsteinTargetRicciCoordinate_zero_of_odd_stationary
    (Q r M a θ : ℝ)
    (i j : Fin 4)
    (hodd : kerrStationarySign i * kerrStationarySign j = -1) :
    kerrEinsteinTargetRicciCoordinate Q r M a θ i j = 0 := by
  have hp :=
    kerrEinsteinTargetRicciCoordinate_stationary_parity
      Q r M a θ i j
  rw [hodd] at hp
  linarith

/-- Hence the full odd-parity sector of the metric Ricci tensor already satisfies the
Einstein-Maxwell Ricci equation, without evaluating any second derivatives. -/
theorem kerrRicciCovFromMetric_eq_target_of_odd_stationary
    (Q r M a θ : ℝ)
    (i j : Fin 4)
    (hodd : kerrStationarySign i * kerrStationarySign j = -1) :
    kerrRicciCovFromMetric r M a Q θ i j =
      kerrEinsteinTargetRicciCoordinate Q r M a θ i j := by
  rw [kerrRicciCovFromMetric_zero_of_odd_stationary
        r M a Q θ i j hodd,
      kerrEinsteinTargetRicciCoordinate_zero_of_odd_stationary
        Q r M a θ i j hodd]

/-- Those eight components already satisfy the Einstein-Maxwell Ricci target exactly. -/
theorem kerrRicci_stationary_meridional_eq_target
    (Q r M a θ : ℝ) :
    kerrRicciCovFromMetric r M a Q θ 0 1 =
        kerrEinsteinTargetRicciCoordinate Q r M a θ 0 1 ∧
    kerrRicciCovFromMetric r M a Q θ 0 2 =
        kerrEinsteinTargetRicciCoordinate Q r M a θ 0 2 ∧
    kerrRicciCovFromMetric r M a Q θ 3 1 =
        kerrEinsteinTargetRicciCoordinate Q r M a θ 3 1 ∧
    kerrRicciCovFromMetric r M a Q θ 3 2 =
        kerrEinsteinTargetRicciCoordinate Q r M a θ 3 2 ∧
    kerrRicciCovFromMetric r M a Q θ 1 0 =
        kerrEinsteinTargetRicciCoordinate Q r M a θ 1 0 ∧
    kerrRicciCovFromMetric r M a Q θ 2 0 =
        kerrEinsteinTargetRicciCoordinate Q r M a θ 2 0 ∧
    kerrRicciCovFromMetric r M a Q θ 1 3 =
        kerrEinsteinTargetRicciCoordinate Q r M a θ 1 3 ∧
    kerrRicciCovFromMetric r M a Q θ 2 3 =
        kerrEinsteinTargetRicciCoordinate Q r M a θ 2 3 := by
  rcases kerrRicci_stationary_meridional_zero r M a Q θ with
    ⟨h01,h02,h31,h32,h10,h20,h13,h23⟩
  simpa [kerrEinsteinTargetRicciCoordinate] using
    And.intro h01
      (And.intro h02
        (And.intro h31
          (And.intro h32
            (And.intro h10
              (And.intro h20
                (And.intro h13 h23))))))

/-- All sixteen Boyer-Lindquist Ricci components now equal the explicit
Einstein-Maxwell target.  This proof uses only the component theorems already
derived from the metric plus stationary-reflection parity and tensor symmetry. -/
theorem kerrRicci_full_eq_target_direct
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    ∀ i j : Fin 4,
      kerrRicciCovFromMetric r M a Q θ i j =
        kerrEinsteinTargetRicciCoordinate Q r M a θ i j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact kerrRicci_tt_eq_target Q r M a θ hsig hdel hsin
  · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
    norm_num [kerrStationarySign]
  · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
    norm_num [kerrStationarySign]
  · exact kerrRicci_tphi_eq_target Q r M a θ hsig hdel hsin
  · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
    norm_num [kerrStationarySign]
  · exact kerrRicci_rr_eq_target Q r M a θ hsig hdel hsin
  · exact kerrRicci_rtheta_eq_target Q r M a θ hsig hdel hsin
  · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
    norm_num [kerrStationarySign]
  · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
    norm_num [kerrStationarySign]
  · exact kerrRicci_thetar_eq_target Q r M a θ hsig hdel hsin
  · exact kerrRicci_thetatheta_eq_target Q r M a θ hsig hdel hsin
  · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
    norm_num [kerrStationarySign]
  · rw [← kerrRicci_tphi_symmetric r M a Q θ,
        ← kerrEinsteinTargetRicciCoordinate_symmetric Q r M a θ 0 3]
    exact kerrRicci_tphi_eq_target Q r M a θ hsig hdel hsin
  · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
    norm_num [kerrStationarySign]
  · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
    norm_num [kerrStationarySign]
  · exact kerrRicci_phiphi_eq_target Q r M a θ hsig hdel hsin

/-- Backward-compatible name for the completed metric-derived Ricci theorem. -/
theorem kerrRicci_full_eq_target
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    ∀ i j : Fin 4,
      kerrRicciCovFromMetric r M a Q θ i j =
        kerrEinsteinTargetRicciCoordinate Q r M a θ i j :=
  kerrRicci_full_eq_target_direct Q r M a θ hsig hdel hsin

/-- The coframe-defined Einstein-Maxwell Ricci target is exactly the explicit coordinate tensor. -/
theorem kerrEinsteinTargetRicciCov_eq_coordinate
    (Q r M a θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (i j : Fin 4) :
    kerrEinsteinTargetRicciCov Q r M a θ i j =
      kerrEinsteinTargetRicciCoordinate Q r M a θ i j := by
  have hS0 : Sigma r a θ ≠ 0 := ne_of_gt hsig
  have hD0 : Delta r M a Q ≠ 0 := ne_of_gt hdel
  have hSD : 0 < Sigma r a θ * Delta r M a Q :=
    mul_pos hsig hdel
  have hSD0 :
      Real.sqrt (Sigma r a θ * Delta r M a Q) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hSD)
  have hSqrtS0 :
      Real.sqrt (Sigma r a θ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hsig)
  have hSDsq :
      (Real.sqrt (Sigma r a θ * Delta r M a Q))^2 =
        Sigma r a θ * Delta r M a Q :=
    Real.sq_sqrt (le_of_lt hSD)
  have hSsq :
      (Real.sqrt (Sigma r a θ))^2 =
        Sigma r a θ :=
    Real.sq_sqrt (le_of_lt hsig)
  fin_cases i <;> fin_cases j <;>
    simp [kerrEinsteinTargetRicciCov,
      kerrEinsteinTargetRicciCoordinate,
      kerrRicciFrameCovCoeff, kerrCoframe,
      kerrCoframe0, kerrCoframe1, kerrCoframe2, kerrCoframe3,
      stationaryCovectorLift, kerrTemporalOneFormCoeffs,
      kerrAxialOneFormCoeffs, principalBasis,
      hS0, hD0, hSD0, hSqrtS0] <;>
    field_simp [hS0, hD0, hSD0, hSqrtS0] <;>
    nlinarith

/-- Coordinate trace of the field-forced Ricci target. -/
def kerrEinsteinTargetRicciTrace
    (Q r M a θ : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    kerrMetricInv r M a Q θ i j *
      kerrEinsteinTargetRicciCov Q r M a θ i j

/-- Generic rank-one trace contraction used to reduce coordinate traces to coframe norms. -/
theorem kerr_rankOne_trace
    (r M a Q θ c : ℝ)
    (α : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      kerrMetricInv r M a Q θ i j *
        (c * α i * α j)) =
      c * kerrCovectorInner r M a Q θ α α := by
  unfold kerrCovectorInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The coordinate trace reduces exactly to the four orthonormal-frame norms. -/
theorem kerrEinsteinTargetRicciTrace_eq_frame_sum
    (Q r M a θ : ℝ) :
    kerrEinsteinTargetRicciTrace Q r M a θ =
      ∑ A : Fin 4,
        kerrRicciFrameCovCoeff Q r a θ A *
          kerrCovectorInner r M a Q θ
            (kerrCoframe r M a Q θ A)
            (kerrCoframe r M a Q θ A) := by
  unfold kerrEinsteinTargetRicciTrace
  simp_rw [kerrEinsteinTargetRicciCov, Finset.mul_sum]
  calc
    (∑ i : Fin 4, ∑ j : Fin 4, ∑ A : Fin 4,
      kerrMetricInv r M a Q θ i j *
        (kerrRicciFrameCovCoeff Q r a θ A *
          kerrCoframe r M a Q θ A i *
          kerrCoframe r M a Q θ A j))
        =
      ∑ i : Fin 4, ∑ A : Fin 4, ∑ j : Fin 4,
        kerrMetricInv r M a Q θ i j *
          (kerrRicciFrameCovCoeff Q r a θ A *
            kerrCoframe r M a Q θ A i *
            kerrCoframe r M a Q θ A j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
    _ =
      ∑ A : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
        kerrMetricInv r M a Q θ i j *
          (kerrRicciFrameCovCoeff Q r a θ A *
            kerrCoframe r M a Q θ A i *
            kerrCoframe r M a Q θ A j) := by
          rw [Finset.sum_comm]
    _ =
      ∑ A : Fin 4,
        kerrRicciFrameCovCoeff Q r a θ A *
          kerrCovectorInner r M a Q θ
            (kerrCoframe r M a Q θ A)
            (kerrCoframe r M a Q θ A) := by
          apply Finset.sum_congr rfl
          intro A hA
          exact kerr_rankOne_trace r M a Q θ
            (kerrRicciFrameCovCoeff Q r a θ A)
            (kerrCoframe r M a Q θ A)

/-- The Einstein-Maxwell Ricci target is trace-free in the actual Kerr metric. -/
theorem kerrEinsteinTargetRicci_trace_zero
    (Q r M a θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (hsin : Real.sin θ ≠ 0) :
    kerrEinsteinTargetRicciTrace Q r M a θ = 0 := by
  rw [kerrEinsteinTargetRicciTrace_eq_frame_sum]
  simp_rw [kerrCoframe_orthonormal
    r M a Q θ hsig hdel hsin]
  simp [Fin.sum_univ_four,
    kerrRicciFrameCovCoeff, principalMetricSign]
  ring

/-! ### Exact finite closure criterion for the remaining Kerr curvature calculation -/

/-- After stationary-reflection parity closes the eight odd components, these are exactly
the eight even ordered Ricci component obligations that remain. -/
def kerrEvenRicciObligations
    (Q r M a θ : ℝ) : Prop :=
  kerrRicciCovFromMetric r M a Q θ 0 0 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 0 ∧
  kerrRicciCovFromMetric r M a Q θ 0 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 3 ∧
  kerrRicciCovFromMetric r M a Q θ 1 1 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 1 1 ∧
  kerrRicciCovFromMetric r M a Q θ 1 2 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 1 2 ∧
  kerrRicciCovFromMetric r M a Q θ 2 1 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 2 1 ∧
  kerrRicciCovFromMetric r M a Q θ 2 2 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 2 2 ∧
  kerrRicciCovFromMetric r M a Q θ 3 0 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 3 0 ∧
  kerrRicciCovFromMetric r M a Q θ 3 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 3 3

/-- The full sixteen-component Ricci equation is equivalent to those eight even obligations;
the other eight components are the already-proved odd-parity sector. -/
theorem kerrFullRicciEquation_iff_even_obligations
    (Q r M a θ : ℝ) :
    (∀ i j : Fin 4,
      kerrRicciCovFromMetric r M a Q θ i j =
        kerrEinsteinTargetRicciCoordinate Q r M a θ i j) ↔
      kerrEvenRicciObligations Q r M a θ := by
  constructor
  · intro h
    exact ⟨h 0 0, h 0 3, h 1 1, h 1 2,
      h 2 1, h 2 2, h 3 0, h 3 3⟩
  · intro h
    rcases h with ⟨h00,h03,h11,h12,h21,h22,h30,h33⟩
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
      norm_num [kerrStationarySign]
    · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
      norm_num [kerrStationarySign]
    · exact h03
    · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
      norm_num [kerrStationarySign]
    · exact h11
    · exact h12
    · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
      norm_num [kerrStationarySign]
    · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
      norm_num [kerrStationarySign]
    · exact h21
    · exact h22
    · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
      norm_num [kerrStationarySign]
    · exact h30
    · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
      norm_num [kerrStationarySign]
    · apply kerrRicciCovFromMetric_eq_target_of_odd_stationary
      norm_num [kerrStationarySign]
    · exact h33

/-- Once the finite even Ricci obligations are discharged, scalar curvature zero and the
full metric-derived Einstein tensor follow automatically from the already-forced
trace-free Einstein-Maxwell target. -/
theorem kerrEinsteinEquation_from_evenRicciObligations
    (Q r M a θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (hsin : Real.sin θ ≠ 0)
    (hEven : kerrEvenRicciObligations Q r M a θ) :
    kerrScalarCurvatureFromMetric r M a Q θ = 0 ∧
    (∀ i j : Fin 4,
      kerrEinsteinCovFromMetric r M a Q θ i j =
        kerrEinsteinTargetRicciCov Q r M a θ i j) := by
  have hRicCoord :
      ∀ i j : Fin 4,
        kerrRicciCovFromMetric r M a Q θ i j =
          kerrEinsteinTargetRicciCoordinate Q r M a θ i j :=
    (kerrFullRicciEquation_iff_even_obligations
      Q r M a θ).2 hEven
  have hTarget :
      ∀ i j : Fin 4,
        kerrEinsteinTargetRicciCov Q r M a θ i j =
          kerrEinsteinTargetRicciCoordinate Q r M a θ i j := by
    intro i j
    exact kerrEinsteinTargetRicciCov_eq_coordinate
      Q r M a θ hsig hdel i j
  have hRicCov :
      ∀ i j : Fin 4,
        kerrRicciCovFromMetric r M a Q θ i j =
          kerrEinsteinTargetRicciCov Q r M a θ i j := by
    intro i j
    rw [hTarget i j]
    exact hRicCoord i j
  have hScalarEq :
      kerrScalarCurvatureFromMetric r M a Q θ =
        kerrEinsteinTargetRicciTrace Q r M a θ := by
    unfold kerrScalarCurvatureFromMetric kerrEinsteinTargetRicciTrace
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hRicCov i j]
  have hScalar : kerrScalarCurvatureFromMetric r M a Q θ = 0 := by
    rw [hScalarEq]
    exact kerrEinsteinTargetRicci_trace_zero
      Q r M a θ hsig hdel hsin
  refine ⟨hScalar, ?_⟩
  intro i j
  unfold kerrEinsteinCovFromMetric
  rw [hScalar]
  simp
  exact hRicCov i j

/-- After the two mixed meridional equations are also derived, only these six ordered
even-parity Ricci components remain to close the Kerr-Newman Einstein equation. -/
def kerrSixRicciObligations
    (Q r M a θ : ℝ) : Prop :=
  kerrRicciCovFromMetric r M a Q θ 0 0 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 0 ∧
  kerrRicciCovFromMetric r M a Q θ 0 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 3 ∧
  kerrRicciCovFromMetric r M a Q θ 1 1 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 1 1 ∧
  kerrRicciCovFromMetric r M a Q θ 2 2 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 2 2 ∧
  kerrRicciCovFromMetric r M a Q θ 3 0 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 3 0 ∧
  kerrRicciCovFromMetric r M a Q θ 3 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 3 3

/-- On the regular Boyer-Lindquist chart, the former eight-component closure condition
is equivalent to the six genuinely unproved components because both r-theta orders
have now been derived from the metric. -/
theorem kerrEvenRicciObligations_iff_six
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrEvenRicciObligations Q r M a θ ↔
      kerrSixRicciObligations Q r M a θ := by
  constructor
  · rintro ⟨h00,h03,h11,_h12,_h21,h22,h30,h33⟩
    exact ⟨h00,h03,h11,h22,h30,h33⟩
  · rintro ⟨h00,h03,h11,h22,h30,h33⟩
    exact ⟨h00,h03,h11,
      kerrRicci_rtheta_eq_target Q r M a θ hsig hdel hsin,
      kerrRicci_thetar_eq_target Q r M a θ hsig hdel hsin,
      h22,h30,h33⟩

/-- Therefore the full sixteen-component Ricci equation is equivalent, on the regular
chart, to exactly six remaining scalar identities. -/
theorem kerrFullRicciEquation_iff_six_obligations
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    (∀ i j : Fin 4,
      kerrRicciCovFromMetric r M a Q θ i j =
        kerrEinsteinTargetRicciCoordinate Q r M a θ i j) ↔
      kerrSixRicciObligations Q r M a θ := by
  exact (kerrFullRicciEquation_iff_even_obligations
    Q r M a θ).trans
      (kerrEvenRicciObligations_iff_six
        Q r M a θ hsig hdel hsin)

/-- Six scalar curvature identities are now sufficient for the complete metric-derived
Einstein tensor, including the forced trace-free reduction. -/
theorem kerrEinsteinEquation_from_sixRicciObligations
    (Q r M a θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (hsin : Real.sin θ ≠ 0)
    (hSix : kerrSixRicciObligations Q r M a θ) :
    kerrScalarCurvatureFromMetric r M a Q θ = 0 ∧
    (∀ i j : Fin 4,
      kerrEinsteinCovFromMetric r M a Q θ i j =
        kerrEinsteinTargetRicciCov Q r M a θ i j) := by
  apply kerrEinsteinEquation_from_evenRicciObligations
    Q r M a θ hsig hdel hsin
  exact (kerrEvenRicciObligations_iff_six
    Q r M a θ (ne_of_gt hsig) (ne_of_gt hdel) hsin).2 hSix

/-- Stationary-block symmetry removes the reverse t-phi equation as an independent
obligation.  These five scalar identities are the remaining Kerr-Newman Ricci block. -/
def kerrFiveRicciObligations
    (Q r M a θ : ℝ) : Prop :=
  kerrRicciCovFromMetric r M a Q θ 0 0 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 0 ∧
  kerrRicciCovFromMetric r M a Q θ 0 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 3 ∧
  kerrRicciCovFromMetric r M a Q θ 1 1 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 1 1 ∧
  kerrRicciCovFromMetric r M a Q θ 2 2 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 2 2 ∧
  kerrRicciCovFromMetric r M a Q θ 3 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 3 3

/-- The six-component closure is equivalent to five components because both the metric
Ricci tensor and the forced target have equal t-phi and phi-t entries. -/
theorem kerrSixRicciObligations_iff_five
    (Q r M a θ : ℝ) :
    kerrSixRicciObligations Q r M a θ ↔
      kerrFiveRicciObligations Q r M a θ := by
  constructor
  · rintro ⟨h00,h03,h11,h22,_h30,h33⟩
    exact ⟨h00,h03,h11,h22,h33⟩
  · rintro ⟨h00,h03,h11,h22,h33⟩
    have h30 :
        kerrRicciCovFromMetric r M a Q θ 3 0 =
          kerrEinsteinTargetRicciCoordinate Q r M a θ 3 0 := by
      rw [← kerrRicci_tphi_symmetric r M a Q θ,
          ← kerrEinsteinTargetRicciCoordinate_symmetric
            Q r M a θ 0 3]
      exact h03
    exact ⟨h00,h03,h11,h22,h30,h33⟩

/-- On the regular chart, the complete sixteen-component Ricci equation has now been
reduced to five scalar curvature identities. -/
theorem kerrFullRicciEquation_iff_five_obligations
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    (∀ i j : Fin 4,
      kerrRicciCovFromMetric r M a Q θ i j =
        kerrEinsteinTargetRicciCoordinate Q r M a θ i j) ↔
      kerrFiveRicciObligations Q r M a θ := by
  exact (kerrFullRicciEquation_iff_six_obligations
    Q r M a θ hsig hdel hsin).trans
      (kerrSixRicciObligations_iff_five Q r M a θ)

/-- Five scalar Ricci identities therefore suffice for the complete metric-derived
Einstein-Maxwell equation on the regular chart. -/
theorem kerrEinsteinEquation_from_fiveRicciObligations
    (Q r M a θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (hsin : Real.sin θ ≠ 0)
    (hFive : kerrFiveRicciObligations Q r M a θ) :
    kerrScalarCurvatureFromMetric r M a Q θ = 0 ∧
    (∀ i j : Fin 4,
      kerrEinsteinCovFromMetric r M a Q θ i j =
        kerrEinsteinTargetRicciCov Q r M a θ i j) := by
  apply kerrEinsteinEquation_from_sixRicciObligations
    Q r M a θ hsig hdel hsin
  exact (kerrSixRicciObligations_iff_five Q r M a θ).2 hFive

/-- With the polar diagonal equation now metric-derived, only four scalar curvature
identities remain: tt, tφ, rr, and φφ. -/
def kerrFourRicciObligations
    (Q r M a θ : ℝ) : Prop :=
  kerrRicciCovFromMetric r M a Q θ 0 0 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 0 ∧
  kerrRicciCovFromMetric r M a Q θ 0 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 3 ∧
  kerrRicciCovFromMetric r M a Q θ 1 1 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 1 1 ∧
  kerrRicciCovFromMetric r M a Q θ 3 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 3 3

/-- On the regular chart, the five-component closure condition is equivalent to the
four components not already discharged by the polar Ricci calculation. -/
theorem kerrFiveRicciObligations_iff_four
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrFiveRicciObligations Q r M a θ ↔
      kerrFourRicciObligations Q r M a θ := by
  constructor
  · rintro ⟨h00,h03,h11,_h22,h33⟩
    exact ⟨h00,h03,h11,h33⟩
  · rintro ⟨h00,h03,h11,h33⟩
    exact ⟨h00,h03,h11,
      kerrRicci_thetatheta_eq_target Q r M a θ hsig hdel hsin,
      h33⟩

/-- Thus the full metric Ricci equation is equivalent to four explicit remaining
component identities on the regular Boyer-Lindquist chart. -/
theorem kerrFullRicciEquation_iff_four_obligations
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    (∀ i j : Fin 4,
      kerrRicciCovFromMetric r M a Q θ i j =
        kerrEinsteinTargetRicciCoordinate Q r M a θ i j) ↔
      kerrFourRicciObligations Q r M a θ := by
  exact (kerrFullRicciEquation_iff_five_obligations
    Q r M a θ hsig hdel hsin).trans
      (kerrFiveRicciObligations_iff_four
        Q r M a θ hsig hdel hsin)

/-- With both meridional diagonal equations closed, only the stationary 2x2 Ricci block
remains: tt, tφ, and φφ. -/
def kerrThreeRicciObligations
    (Q r M a θ : ℝ) : Prop :=
  kerrRicciCovFromMetric r M a Q θ 0 0 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 0 ∧
  kerrRicciCovFromMetric r M a Q θ 0 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 3 ∧
  kerrRicciCovFromMetric r M a Q θ 3 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 3 3

theorem kerrFourRicciObligations_iff_three
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrFourRicciObligations Q r M a θ ↔
      kerrThreeRicciObligations Q r M a θ := by
  constructor
  · rintro ⟨h00,h03,_h11,h33⟩
    exact ⟨h00,h03,h33⟩
  · rintro ⟨h00,h03,h33⟩
    exact ⟨h00,h03,
      kerrRicci_rr_eq_target Q r M a θ hsig hdel hsin, h33⟩

/-- The entire Kerr-Newman Ricci calculation is therefore reduced to the stationary
two-by-two block alone. -/
theorem kerrFullRicciEquation_iff_three_obligations
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    (∀ i j : Fin 4,
      kerrRicciCovFromMetric r M a Q θ i j =
        kerrEinsteinTargetRicciCoordinate Q r M a θ i j) ↔
      kerrThreeRicciObligations Q r M a θ := by
  exact (kerrFullRicciEquation_iff_four_obligations
    Q r M a θ hsig hdel hsin).trans
      (kerrFourRicciObligations_iff_three
        Q r M a θ hsig hdel hsin)

/-- After deriving R_tt, only the t-phi and phi-phi stationary equations remain. -/
def kerrTwoRicciObligations
    (Q r M a θ : ℝ) : Prop :=
  kerrRicciCovFromMetric r M a Q θ 0 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 0 3 ∧
  kerrRicciCovFromMetric r M a Q θ 3 3 =
      kerrEinsteinTargetRicciCoordinate Q r M a θ 3 3

theorem kerrThreeRicciObligations_iff_two
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrThreeRicciObligations Q r M a θ ↔
      kerrTwoRicciObligations Q r M a θ := by
  constructor
  · rintro ⟨_h00,h03,h33⟩
    exact ⟨h03,h33⟩
  · rintro ⟨h03,h33⟩
    exact ⟨kerrRicci_tt_eq_target Q r M a θ hsig hdel hsin,h03,h33⟩

theorem kerrFullRicciEquation_iff_two_obligations
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    (∀ i j : Fin 4,
      kerrRicciCovFromMetric r M a Q θ i j =
        kerrEinsteinTargetRicciCoordinate Q r M a θ i j) ↔
      kerrTwoRicciObligations Q r M a θ := by
  exact (kerrFullRicciEquation_iff_three_obligations
    Q r M a θ hsig hdel hsin).trans
      (kerrThreeRicciObligations_iff_two
        Q r M a θ hsig hdel hsin)

/-- After deriving R_tphi, the entire Kerr-Newman curvature calculation has one
remaining scalar component: R_phiphi. -/
def kerrOneRicciObligation
    (Q r M a θ : ℝ) : Prop :=
  kerrRicciCovFromMetric r M a Q θ 3 3 =
    kerrEinsteinTargetRicciCoordinate Q r M a θ 3 3

theorem kerrTwoRicciObligations_iff_one
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrTwoRicciObligations Q r M a θ ↔
      kerrOneRicciObligation Q r M a θ := by
  constructor
  · rintro ⟨_h03,h33⟩
    exact h33
  · intro h33
    exact ⟨kerrRicci_tphi_eq_target Q r M a θ hsig hdel hsin,h33⟩

theorem kerrFullRicciEquation_iff_one_obligation
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    (∀ i j : Fin 4,
      kerrRicciCovFromMetric r M a Q θ i j =
        kerrEinsteinTargetRicciCoordinate Q r M a θ i j) ↔
      kerrOneRicciObligation Q r M a θ := by
  exact (kerrFullRicciEquation_iff_two_obligations
    Q r M a θ hsig hdel hsin).trans
      (kerrTwoRicciObligations_iff_one
        Q r M a θ hsig hdel hsin)

/-- Mixed Ricci eigenvalue obtained by raising the first Carter-frame index. -/
def kerrRicciFrameMixedCoeff
    (Q r a θ : ℝ) (A : Fin 4) : ℝ :=
  principalMetricSign A *
    kerrRicciFrameCovCoeff Q r a θ A

/-- The potential-derived Maxwell energy density is exactly q/(8π). -/
theorem kerrPrincipalEnergyDensity_formula
    (Q r a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0) :
    principalFieldEnergyDensity
        (kerrPrincipalE Q r a θ)
        (kerrPrincipalB Q r a θ) =
      kerrRicciScale Q r a θ / (8 * Real.pi) := by
  unfold principalFieldEnergyDensity kerrRicciScale
  rw [kerrPrincipal_field_magnitude Q r a θ hsig]
  rfl

/-- Every mixed Carter-frame Ricci target eigenvalue is exactly the
Einstein-Maxwell source 8π T^A_A of the explicit field. -/
theorem kerrRicciFrameMixedCoeff_eq_EinsteinMaxwell
    (Q r a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (A : Fin 4) :
    kerrRicciFrameMixedCoeff Q r a θ A =
      8 * Real.pi *
        principalStress
          (principalFieldEnergyDensity
            (kerrPrincipalE Q r a θ)
            (kerrPrincipalB Q r a θ))
          A A := by
  rw [kerrPrincipalEnergyDensity_formula Q r a θ hsig]
  fin_cases A <;>
    simp [kerrRicciFrameMixedCoeff,
      kerrRicciFrameCovCoeff,
      principalMetricSign, principalStress] <;>
    field_simp [ne_of_gt Real.pi_pos] <;>
    ring

/-- Off-diagonal Carter-frame Einstein-Maxwell source components vanish. -/
theorem kerrEinsteinMaxwellFrame_offdiag
    (Q r a θ : ℝ)
    (A B : Fin 4)
    (hAB : A ≠ B) :
    8 * Real.pi *
      principalStress
        (principalFieldEnergyDensity
          (kerrPrincipalE Q r a θ)
          (kerrPrincipalB Q r a θ))
        A B = 0 := by
  simp [principalStress, hAB]

/-- Thus the field-forced mixed Ricci target is exactly the full diagonal
Einstein-Maxwell source in the metric-selected Carter frame. -/
theorem kerrEinsteinTarget_frame_equation
    (Q r a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (A B : Fin 4) :
    (if A = B then kerrRicciFrameMixedCoeff Q r a θ A else 0) =
      8 * Real.pi *
        principalStress
          (principalFieldEnergyDensity
            (kerrPrincipalE Q r a θ)
            (kerrPrincipalB Q r a θ))
          A B := by
  by_cases h : A = B
  · subst B
    simp [kerrRicciFrameMixedCoeff_eq_EinsteinMaxwell
      Q r a θ hsig A]
  · rw [if_neg h,
      kerrEinsteinMaxwellFrame_offdiag Q r a θ A B h]

/-- Covariant Carter-frame Ricci coefficient is exactly `8π` times the
covariant Maxwell stress coefficient of the potential-derived principal field. -/
theorem kerrRicciFrameCovCoeff_eq_EinsteinMaxwellCov
    (Q r a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (A : Fin 4) :
    kerrRicciFrameCovCoeff Q r a θ A =
      8 * Real.pi *
        (principalMetricSign A *
          principalStress
            (principalFieldEnergyDensity
              (kerrPrincipalE Q r a θ)
              (kerrPrincipalB Q r a θ)) A A) := by
  rw [kerrPrincipalEnergyDensity_formula Q r a θ hsig]
  fin_cases A <;>
    simp [kerrRicciFrameCovCoeff, principalMetricSign,
      principalStress, kerrRicciScale] <;>
    field_simp [ne_of_gt Real.pi_pos] <;>
    ring

/-- Boyer-Lindquist covariant Maxwell stress obtained by pushing the
potential-derived principal stress through the metric-selected Carter coframe. -/
def kerrMaxwellStressCovFromPotential
    (Q r M a θ : ℝ) (i j : Fin 4) : ℝ :=
  ∑ A : Fin 4,
    (principalMetricSign A *
      principalStress
        (principalFieldEnergyDensity
          (kerrPrincipalE Q r a θ)
          (kerrPrincipalB Q r a θ)) A A) *
      kerrCoframe r M a Q θ A i *
      kerrCoframe r M a Q θ A j

/-- The coframe Ricci target is exactly `8π T_ab[F]` for that
potential-derived Maxwell field. -/
theorem kerrEinsteinTargetRicciCov_eq_8pi_MaxwellStress
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (i j : Fin 4) :
    kerrEinsteinTargetRicciCov Q r M a Q θ i j =
      8 * Real.pi *
        kerrMaxwellStressCovFromPotential Q r M a θ i j := by
  unfold kerrEinsteinTargetRicciCov
    kerrMaxwellStressCovFromPotential
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [kerrRicciFrameCovCoeff_eq_EinsteinMaxwellCov
    Q r a θ hsig A]
  ring

/-- The metric-derived Kerr-Newman scalar curvature vanishes on the regular
Carter chart because the full Ricci tensor equals the trace-free Maxwell target. -/
theorem kerrScalarCurvatureFromMetric_zero
    (Q r M a θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (hsin : Real.sin θ ≠ 0) :
    kerrScalarCurvatureFromMetric r M a Q θ = 0 := by
  have htrace :
      kerrScalarCurvatureFromMetric r M a Q θ =
        kerrEinsteinTargetRicciTrace Q r M a θ := by
    unfold kerrScalarCurvatureFromMetric kerrEinsteinTargetRicciTrace
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [kerrRicci_full_eq_target Q r M a θ
      (ne_of_gt hsig) (ne_of_gt hdel) hsin i j]
    rw [← kerrEinsteinTargetRicciCov_eq_coordinate
      Q r M a θ hsig hdel i j]
  rw [htrace]
  exact kerrEinsteinTargetRicci_trace_zero
    Q r M a θ hsig hdel hsin

/-- Full Einstein equation in Boyer-Lindquist coordinates: the Einstein tensor
computed from the metric equals `8π` times the potential-derived Maxwell stress. -/
theorem kerrEinsteinCovFromMetric_eq_8pi_MaxwellStress
    (Q r M a θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (hsin : Real.sin θ ≠ 0) :
    ∀ i j : Fin 4,
      kerrEinsteinCovFromMetric r M a Q θ i j =
        8 * Real.pi *
          kerrMaxwellStressCovFromPotential Q r M a θ i j := by
  intro i j
  unfold kerrEinsteinCovFromMetric
  rw [kerrScalarCurvatureFromMetric_zero
    Q r M a θ hsig hdel hsin]
  simp
  rw [kerrRicci_full_eq_target Q r M a θ
    (ne_of_gt hsig) (ne_of_gt hdel) hsin i j]
  rw [← kerrEinsteinTargetRicciCov_eq_coordinate
    Q r M a θ hsig hdel i j]
  exact kerrEinsteinTargetRicciCov_eq_8pi_MaxwellStress
    Q r M a θ (ne_of_gt hsig) i j


/-- The frame invariant squared Ricci norm of the target is four times q squared. -/
def kerrEinsteinTargetRicciFrameNormSq
    (Q r a θ : ℝ) : ℝ :=
  ∑ A : Fin 4,
    (kerrRicciFrameCovCoeff Q r a θ A)^2

theorem kerrEinsteinTargetRicci_frame_norm
    (Q r a θ : ℝ) :
    kerrEinsteinTargetRicciFrameNormSq Q r a θ =
      4 * (kerrRicciScale Q r a θ)^2 := by
  unfold kerrEinsteinTargetRicciFrameNormSq
  simp [kerrRicciFrameCovCoeff]
  ring

/-- Hence the field-forced target carries exactly the manuscript invariant
4 Q^4 / Sigma^4. -/
theorem kerrEinsteinTargetRicci_frame_norm_formula
    (Q r a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0) :
    kerrEinsteinTargetRicciFrameNormSq Q r a θ =
      4 * Q^4 / (Sigma r a θ)^4 := by
  rw [kerrEinsteinTargetRicci_frame_norm]
  unfold kerrRicciScale
  field_simp [hsig]
  ring

/-- Coordinate Maxwell two-form reconstructed from the four derivatives of the
Boyer-Lindquist potential. -/
def kerrCoordinateField
    (Q r a θ : ℝ) (i j : Fin 4) : ℝ :=
  kerrPrincipalE Q r a θ *
      covectorWedge4
        (principalBasis 1)
        (stationaryCovectorLift
          (kerrTemporalOneFormCoeffs a θ)) i j
    + (-kerrPrincipalB Q r a θ * Real.sin θ) *
      covectorWedge4
        (principalBasis 2)
        (stationaryCovectorLift
          (kerrAxialOneFormCoeffs r a)) i j

/-- The coordinate field has exactly the four nonzero derivative components obtained
from `F=dA`. -/
theorem kerrCoordinateField_components
    (Q r a θ : ℝ) :
    kerrCoordinateField Q r a θ 1 0 =
        kerrPrincipalE Q r a θ ∧
    kerrCoordinateField Q r a θ 1 3 =
        -a * (Real.sin θ)^2 *
          kerrPrincipalE Q r a θ ∧
    kerrCoordinateField Q r a θ 2 0 =
        -a * Real.sin θ *
          kerrPrincipalB Q r a θ ∧
    kerrCoordinateField Q r a θ 2 3 =
        (r^2 + a^2) * Real.sin θ *
          kerrPrincipalB Q r a θ := by
  constructor
  · simp [kerrCoordinateField, covectorWedge4,
      principalBasis, stationaryCovectorLift,
      kerrTemporalOneFormCoeffs, kerrAxialOneFormCoeffs]
  · constructor
    · simp [kerrCoordinateField, covectorWedge4,
        principalBasis, stationaryCovectorLift,
        kerrTemporalOneFormCoeffs, kerrAxialOneFormCoeffs]
      ring
    · constructor
      · simp [kerrCoordinateField, covectorWedge4,
          principalBasis, stationaryCovectorLift,
          kerrTemporalOneFormCoeffs, kerrAxialOneFormCoeffs]
        ring
      · simp [kerrCoordinateField, covectorWedge4,
          principalBasis, stationaryCovectorLift,
          kerrTemporalOneFormCoeffs, kerrAxialOneFormCoeffs]
        ring


/-- Raised radial-time component computed from the inverse metric and coordinate field. -/
def kerrRaisedFrt
    (Q r M a θ : ℝ) : ℝ :=
  kerrInvGrr r M a Q θ *
    (kerrInvGtt r M a Q θ *
        kerrCoordinateField Q r a θ 1 0 +
      kerrInvGtPhi r M a Q θ *
        kerrCoordinateField Q r a θ 1 3)

/-- Raised radial-azimuthal component. -/
def kerrRaisedFrPhi
    (Q r M a θ : ℝ) : ℝ :=
  kerrInvGrr r M a Q θ *
    (kerrInvGtPhi r M a Q θ *
        kerrCoordinateField Q r a θ 1 0 +
      kerrInvGPhiPhi r M a Q θ *
        kerrCoordinateField Q r a θ 1 3)

/-- Raised polar-time component. -/
def kerrRaisedFthetaT
    (Q r M a θ : ℝ) : ℝ :=
  kerrInvGthetaTheta r a θ *
    (kerrInvGtt r M a Q θ *
        kerrCoordinateField Q r a θ 2 0 +
      kerrInvGtPhi r M a Q θ *
        kerrCoordinateField Q r a θ 2 3)

/-- Raised polar-azimuthal component. -/
def kerrRaisedFthetaPhi
    (Q r M a θ : ℝ) : ℝ :=
  kerrInvGthetaTheta r a θ *
    (kerrInvGtPhi r M a Q θ *
        kerrCoordinateField Q r a θ 2 0 +
      kerrInvGPhiPhi r M a Q θ *
        kerrCoordinateField Q r a θ 2 3)

/-- Raising the explicit coordinate field produces the standard principal expressions. -/
theorem kerrRaisedField_components
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrRaisedFrt Q r M a θ =
        -(r^2 + a^2) / Sigma r a θ *
          kerrPrincipalE Q r a θ ∧
    kerrRaisedFrPhi Q r M a θ =
        -a / Sigma r a θ *
          kerrPrincipalE Q r a θ ∧
    kerrRaisedFthetaT Q r M a θ =
        a * Real.sin θ / Sigma r a θ *
          kerrPrincipalB Q r a θ ∧
    kerrRaisedFthetaPhi Q r M a θ =
        1 / (Sigma r a θ * Real.sin θ) *
          kerrPrincipalB Q r a θ := by
  rcases kerrCoordinateField_components Q r a θ with
    ⟨hrt, hrp, hθt, hθp⟩
  have htrig :
      (Real.sin θ)^2 = 1 - (Real.cos θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  constructor
  · unfold kerrRaisedFrt kerrInvGrr kerrInvGtt kerrInvGtPhi
    rw [hrt, hrp, htrig]
    field_simp [hsig, hdel]
    unfold Sigma
    ring
  · constructor
    · unfold kerrRaisedFrPhi kerrInvGrr kerrInvGtPhi kerrInvGPhiPhi
      rw [hrt, hrp, htrig]
      field_simp [hsig, hdel, hsin]
      unfold Sigma
      ring
    · constructor
      · unfold kerrRaisedFthetaT kerrInvGthetaTheta kerrInvGtt kerrInvGtPhi
        rw [hθt, hθp, htrig]
        field_simp [hsig, hdel]
        unfold Sigma
        ring
      · unfold kerrRaisedFthetaPhi kerrInvGthetaTheta kerrInvGtPhi kerrInvGPhiPhi
        rw [hθt, hθp, htrig]
        field_simp [hsig, hdel, hsin]
        unfold Sigma
        ring

/-- Multiplying the raised field by the metric volume density reproduces exactly the
four densitized fluxes used in the source-free Maxwell equations. -/
theorem kerrDensitizedField_from_metric
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrVolumeDensity r a θ * kerrRaisedFrt Q r M a θ =
        kerrDensitizedFrt Q r a θ ∧
    kerrVolumeDensity r a θ * kerrRaisedFrPhi Q r M a θ =
        kerrDensitizedFrPhi Q r a θ ∧
    kerrVolumeDensity r a θ * kerrRaisedFthetaT Q r M a θ =
        kerrDensitizedFthetaT Q r a θ ∧
    kerrVolumeDensity r a θ * kerrRaisedFthetaPhi Q r M a θ =
        kerrDensitizedFthetaPhi Q r a θ := by
  rcases kerrRaisedField_components Q r M a θ hsig hdel hsin with
    ⟨hrt, hrp, hθt, hθp⟩
  constructor
  · rw [hrt]
    unfold kerrVolumeDensity kerrDensitizedFrt
    field_simp [hsig]
    ring
  · constructor
    · rw [hrp]
      unfold kerrVolumeDensity kerrDensitizedFrPhi
      field_simp [hsig]
      ring
    · constructor
      · rw [hθt]
        unfold kerrVolumeDensity kerrDensitizedFthetaT
        field_simp [hsig]
        ring
      · rw [hθp]
        unfold kerrVolumeDensity kerrDensitizedFthetaPhi
        field_simp [hsig, hsin]
        ring

/-- The two previously proved divergence identities are therefore literally the
source-free Maxwell equations for the metric-raised field in the regular
Boyer-Lindquist chart. -/
theorem kerrMaxwell_source_free_certificate
    (Q r M a θ : ℝ)
    (hsig : Sigma r a θ ≠ 0)
    (hdel : Delta r M a Q ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    kerrVolumeDensity r a θ * kerrRaisedFrt Q r M a θ =
        kerrDensitizedFrt Q r a θ ∧
    kerrVolumeDensity r a θ * kerrRaisedFrPhi Q r M a θ =
        kerrDensitizedFrPhi Q r a θ ∧
    kerrVolumeDensity r a θ * kerrRaisedFthetaT Q r M a θ =
        kerrDensitizedFthetaT Q r a θ ∧
    kerrVolumeDensity r a θ * kerrRaisedFthetaPhi Q r M a θ =
        kerrDensitizedFthetaPhi Q r a θ ∧
    deriv (fun x : ℝ => kerrDensitizedFrt Q x a θ) r +
        deriv (fun x : ℝ => kerrDensitizedFthetaT Q r a x) θ = 0 ∧
    deriv (fun x : ℝ => kerrDensitizedFrPhi Q x a θ) r +
        deriv (fun x : ℝ => kerrDensitizedFthetaPhi Q r a x) θ = 0 := by
  rcases kerrDensitizedField_from_metric
    Q r M a θ hsig hdel hsin with
    ⟨hrt, hrp, hθt, hθp⟩
  exact ⟨hrt, hrp, hθt, hθp,
    kerrMaxwell_divergence_t Q r a θ hsig,
    kerrMaxwell_divergence_phi Q r a θ hsig⟩

/-- Maxwell field written in the Carter orthonormal coframe.  The overall minus sign is
the orientation induced by `dr∧(dt-a sin²θ dφ)=-e⁰∧e¹`. -/
def kerrFieldInCarterCoframe
    (Q r M a θ : ℝ) (i j : Fin 4) : ℝ :=
  -kerrPrincipalE Q r a θ *
      covectorWedge4
        (kerrCoframe0 r M a Q θ)
        (kerrCoframe1 r M a Q θ) i j
    - kerrPrincipalB Q r a θ *
      covectorWedge4
        (kerrCoframe2 r a θ)
        (kerrCoframe3 r a θ) i j

/-- On the regular exterior, the potential-derived coordinate field is exactly the
principal Carter-coframe field `-E e⁰∧e¹-B e²∧e³`. -/
theorem kerrCoordinateField_eq_CarterCoframe
    (Q r M a θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q) :
    kerrCoordinateField Q r a θ =
      kerrFieldInCarterCoframe Q r M a θ := by
  have hS0 : Real.sqrt (Sigma r a θ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hsig)
  have hSDpos :
      0 < Sigma r a θ * Delta r M a Q :=
    mul_pos hsig hdel
  have hSD0 :
      Real.sqrt (Sigma r a θ * Delta r M a Q) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hSDpos)
  have hD0 : Delta r M a Q ≠ 0 := ne_of_gt hdel
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [kerrCoordinateField, kerrFieldInCarterCoframe,
      kerrCoframe0, kerrCoframe1, kerrCoframe2, kerrCoframe3,
      covectorWedge4, principalBasis, stationaryCovectorLift,
      kerrTemporalOneFormCoeffs, kerrAxialOneFormCoeffs,
      hS0, hSD0, hD0] <;>
    field_simp [hS0, hSD0, hD0] <;>
    ring

/-- The Kerr-Newman electromagnetic principal scalars used by the Rainich chain are thus
derived from the explicit potential and the metric-selected Carter coframe. -/
theorem kerrPotential_to_CarterPrincipalField
    (Q r M a θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q) :
    kerrCoordinateField Q r a θ =
      kerrFieldInCarterCoframe Q r M a θ ∧
    kerrCoordinateField Q r a θ 1 0 =
      kerrPrincipalE Q r a θ ∧
    kerrCoordinateField Q r a θ 2 0 =
      -a * Real.sin θ * kerrPrincipalB Q r a θ := by
  exact ⟨kerrCoordinateField_eq_CarterCoframe
      Q r M a θ hsig hdel,
    (kerrCoordinateField_components Q r a θ).1,
    (kerrCoordinateField_components Q r a θ).2.2.1⟩

/-- Complete regular-chart Kerr-Newman Einstein-Maxwell certificate from the
Boyer-Lindquist metric and electromagnetic potential: the metric Einstein tensor
equals the stress of the potential-derived field, the coordinate field is the
Carter-principal field, and all nontrivial Maxwell equations vanish. -/
theorem kerrNewman_full_einstein_maxwell_from_potential
    (Q r M a θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (hsin : Real.sin θ ≠ 0) :
    (∀ i j : Fin 4,
      kerrEinsteinCovFromMetric r M a Q θ i j =
        8 * Real.pi *
          kerrMaxwellStressCovFromPotential Q r M a θ i j) ∧
    kerrCoordinateField Q r a θ =
      kerrFieldInCarterCoframe Q r M a θ ∧
    (deriv
        (fun x : ℝ =>
          -a * Real.sin θ * kerrPrincipalB Q x a θ) r -
      deriv
        (fun x : ℝ =>
          kerrPrincipalE Q r a x) θ = 0 ∧
     deriv
        (fun x : ℝ =>
          (x^2 + a^2) * Real.sin θ *
            kerrPrincipalB Q x a θ) r -
      deriv
        (fun x : ℝ =>
          -a * (Real.sin x)^2 *
            kerrPrincipalE Q r a x) θ = 0 ∧
     deriv (fun x : ℝ => kerrDensitizedFrt Q x a θ) r +
       deriv (fun x : ℝ => kerrDensitizedFthetaT Q r a x) θ = 0 ∧
     deriv (fun x : ℝ => kerrDensitizedFrPhi Q x a θ) r +
       deriv (fun x : ℝ => kerrDensitizedFthetaPhi Q r a x) θ = 0) := by
  refine ⟨kerrEinsteinCovFromMetric_eq_8pi_MaxwellStress
      Q r M a θ hsig hdel hsin,
    kerrCoordinateField_eq_CarterCoframe Q r M a θ hsig hdel, ?_⟩
  exact kerrMaxwell_equations_scalar_certificate
    Q r a θ (ne_of_gt hsig)


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


/-- Stationary `(t,φ)` quadratic form read directly from the square-form
Kerr-Newman metric. -/
def kerrStationaryNormSq
    (r M a Q θ : ℝ) (v : R2) : ℝ :=
  -(Delta r M a Q / Sigma r a θ) *
      (v.1 - a * (Real.sin θ)^2 * v.2)^2
    + ((Real.sin θ)^2 / Sigma r a θ) *
      (a * v.1 - (r^2 + a^2) * v.2)^2

/-- The first Carter stationary combination collapses exactly to `Σ`. -/
theorem carterNumerator_time_leg (r a θ : ℝ) :
    (carterNumerator r a).1 -
        a * (Real.sin θ)^2 * (carterNumerator r a).2 =
      Sigma r a θ := by
  unfold carterNumerator
  have htrig : 1 - (Real.sin θ)^2 = (Real.cos θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    r^2 + a^2 - a * (Real.sin θ)^2 * a
        = r^2 + a^2 * (1 - (Real.sin θ)^2) := by ring
    _ = r^2 + a^2 * (Real.cos θ)^2 := by rw [htrig]
    _ = Sigma r a θ := rfl

/-- The orthogonal stationary square-form combination vanishes on the Carter direction. -/
theorem carterNumerator_axial_leg (r a : ℝ) :
    a * (carterNumerator r a).1 -
        (r^2 + a^2) * (carterNumerator r a).2 = 0 := by
  unfold carterNumerator
  ring

/-- The stationary quadratic form is homogeneous of degree two. -/
theorem kerrStationaryNormSq_smul
    (r M a Q θ c : ℝ) (v : R2) :
    kerrStationaryNormSq r M a Q θ (c • v) =
      c^2 * kerrStationaryNormSq r M a Q θ v := by
  rcases v with ⟨vt, vphi⟩
  simp [kerrStationaryNormSq, pow_two]
  ring

/-- The unnormalized Carter stationary vector has norm exactly `-ΣΔ`. -/
theorem carterNumerator_norm
    (r M a Q θ : ℝ)
    (hsig : Sigma r a θ ≠ 0) :
    kerrStationaryNormSq r M a Q θ (carterNumerator r a) =
      - Sigma r a θ * Delta r M a Q := by
  unfold kerrStationaryNormSq
  rw [carterNumerator_time_leg r a θ,
    carterNumerator_axial_leg r a]
  simp
  field_simp [hsig]
  ring

/-- Metric-normalized Carter observer in the stationary plane. -/
def carterObserver
    (r M a Q θ : ℝ) : R2 :=
  (Real.sqrt (Sigma r a θ * Delta r M a Q))⁻¹ •
    carterNumerator r a

/-- In the regular exterior sector `Σ>0, Δ>0`, the Carter observer is unit timelike
for the Kerr-Newman metric. -/
theorem carterObserver_unit_timelike
    (r M a Q θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q) :
    kerrStationaryNormSq r M a Q θ
      (carterObserver r M a Q θ) = -1 := by
  rw [carterObserver, kerrStationaryNormSq_smul,
    carterNumerator_norm r M a Q θ (ne_of_gt hsig)]
  have hp : 0 < Sigma r a θ * Delta r M a Q :=
    mul_pos hsig hdel
  have hs :
      (Real.sqrt (Sigma r a θ * Delta r M a Q))^2 =
        Sigma r a θ * Delta r M a Q :=
    Real.sq_sqrt (le_of_lt hp)
  have hs0 :
      Real.sqrt (Sigma r a θ * Delta r M a Q) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hp)
  have hc :
      (Real.sqrt (Sigma r a θ * Delta r M a Q))⁻¹ ^ 2 *
        (Sigma r a θ * Delta r M a Q) = 1 := by
    rw [← hs]
    field_simp [hs0]
  calc
    (Real.sqrt (Sigma r a θ * Delta r M a Q))⁻¹ ^ 2 *
        (-Sigma r a θ * Delta r M a Q)
        =
      -((Real.sqrt (Sigma r a θ * Delta r M a Q))⁻¹ ^ 2 *
        (Sigma r a θ * Delta r M a Q)) := by ring
    _ = -1 := by rw [hc]


/-- Normalized temporal Carter coframe coefficient, written without a square-root quotient:
`e⁰ = (Δ/sqrt(ΣΔ))(dt-a sin²θ dφ)`. -/
def carterTemporalCoframeCoeffs
    (r M a Q θ : ℝ) : R2 :=
  (Delta r M a Q /
      Real.sqrt (Sigma r a θ * Delta r M a Q)) •
    kerrTemporalOneFormCoeffs a θ

/-- The normalized Carter observer evaluates to one on the temporal principal coframe. -/
theorem carterTemporalCoframe_on_observer
    (r M a Q θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q) :
    opticalEval
      (carterTemporalCoframeCoeffs r M a Q θ)
      (carterObserver r M a Q θ) = 1 := by
  have hp : 0 < Sigma r a θ * Delta r M a Q :=
    mul_pos hsig hdel
  have hs0 :
      Real.sqrt (Sigma r a θ * Delta r M a Q) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hp)
  have hs :
      (Real.sqrt (Sigma r a θ * Delta r M a Q))^2 =
        Sigma r a θ * Delta r M a Q :=
    Real.sq_sqrt (le_of_lt hp)
  have hleg :
      opticalEval
        (kerrTemporalOneFormCoeffs a θ)
        (carterNumerator r a) =
      Sigma r a θ := by
    unfold opticalEval kerrTemporalOneFormCoeffs
    simpa using carterNumerator_time_leg r a θ
  unfold carterTemporalCoframeCoeffs carterObserver
  have hscale :
      opticalEval
        ((Delta r M a Q /
            Real.sqrt (Sigma r a θ * Delta r M a Q)) •
          kerrTemporalOneFormCoeffs a θ)
        ((Real.sqrt (Sigma r a θ * Delta r M a Q))⁻¹ •
          carterNumerator r a)
      =
      (Delta r M a Q /
          Real.sqrt (Sigma r a θ * Delta r M a Q)) *
        (Real.sqrt (Sigma r a θ * Delta r M a Q))⁻¹ *
        opticalEval
          (kerrTemporalOneFormCoeffs a θ)
          (carterNumerator r a) := by
    unfold opticalEval
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hscale, hleg]
  field_simp [hs0]
  nlinarith

/-- The same Carter observer annihilates the complementary principal stationary one-form. -/
theorem carterAxialOneForm_on_observer
    (r M a Q θ : ℝ) :
    opticalEval
      (kerrAxialOneFormCoeffs r a)
      (carterObserver r M a Q θ) = 0 := by
  have hax :
      opticalEval
        (kerrAxialOneFormCoeffs r a)
        (carterNumerator r a) = 0 := by
    unfold opticalEval kerrAxialOneFormCoeffs
    simpa using carterNumerator_axial_leg r a
  unfold carterObserver
  unfold opticalEval at hax ⊢
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [← mul_add, hax, mul_zero]

/-- The potential-derived Maxwell field blocks and the metric-normalized Carter observer
therefore share the same principal stationary coframe. -/
theorem kerrMaxwell_Carter_principal_structure
    (Q r M a θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q) :
    kerrRadialFieldBlock Q r a θ =
        (kerrPrincipalE Q r a θ) •
          kerrTemporalOneFormCoeffs a θ ∧
    kerrPolarFieldBlock Q r a θ =
        (-kerrPrincipalB Q r a θ * Real.sin θ) •
          kerrAxialOneFormCoeffs r a ∧
    opticalEval
      (carterTemporalCoframeCoeffs r M a Q θ)
      (carterObserver r M a Q θ) = 1 ∧
    opticalEval
      (kerrAxialOneFormCoeffs r a)
      (carterObserver r M a Q θ) = 0 := by
  exact ⟨kerrRadialFieldBlock_carter_aligned Q r a θ,
    kerrPolarFieldBlock_carter_aligned Q r a θ,
    carterTemporalCoframe_on_observer r M a Q θ hsig hdel,
    carterAxialOneForm_on_observer r M a Q θ⟩

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


/-- Full regular-exterior Carter certificate using the first finite resolving carrier jet:
the selected boost is zero, the stationary angular velocity is Carter's, and the resulting
metric-normalized observer is unit timelike. -/
theorem kerr_relative_rest_carter_regular
    (r M a Q θ : ℝ)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q) :
    sigmaStar
      (kerrResolvingQMinus r a θ)
      (kerrResolvingQPlus r a θ) = 0 ∧
    (carterNumerator r a).2 / (carterNumerator r a).1 =
      carterOmega r a ∧
    kerrStationaryNormSq r M a Q θ
      (carterObserver r M a Q θ) = -1 := by
  exact ⟨kerrResolving_balance_rapidity_zero
      r a θ (ne_of_gt hsig),
    carterNumerator_angular_velocity r a,
    carterObserver_unit_timelike r M a Q θ hsig hdel⟩

/-- End-to-end Kerr-Newman specialization certificate from the explicit
Boyer-Lindquist metric and potential, stopping exactly before the still-unformalized
Christoffel/Ricci verification of the Einstein equation. -/
theorem kerrNewman_forced_specialization_certificate
    (Q r M a θ dt dlam : ℝ)
    (hQ : Q ≠ 0)
    (hsig : 0 < Sigma r a θ)
    (hdel : 0 < Delta r M a Q)
    (hsin : 0 < Real.sin θ)
    (hmino : dlam = dt / Sigma r a θ) :
    kerrCoordinateField Q r a θ =
      kerrFieldInCarterCoframe Q r M a θ ∧
    (deriv
        (fun x : ℝ =>
          -a * Real.sin θ * kerrPrincipalB Q x a θ) r -
      deriv
        (fun x : ℝ =>
          kerrPrincipalE Q r a x) θ = 0 ∧
     deriv
        (fun x : ℝ =>
          (x^2 + a^2) * Real.sin θ *
            kerrPrincipalB Q x a θ) r -
      deriv
        (fun x : ℝ =>
          -a * (Real.sin x)^2 *
            kerrPrincipalE Q r a x) θ = 0 ∧
     deriv (fun x : ℝ => kerrDensitizedFrt Q x a θ) r +
       deriv (fun x : ℝ => kerrDensitizedFthetaT Q r a x) θ = 0 ∧
     deriv (fun x : ℝ => kerrDensitizedFrPhi Q x a θ) r +
       deriv (fun x : ℝ => kerrDensitizedFthetaPhi Q r a x) θ = 0) ∧
    (kerrVolumeDensity r a θ * kerrRaisedFrt Q r M a θ =
        kerrDensitizedFrt Q r a θ ∧
     kerrVolumeDensity r a θ * kerrRaisedFrPhi Q r M a θ =
        kerrDensitizedFrPhi Q r a θ ∧
     kerrVolumeDensity r a θ * kerrRaisedFthetaT Q r M a θ =
        kerrDensitizedFthetaT Q r a θ ∧
     kerrVolumeDensity r a θ * kerrRaisedFthetaPhi Q r M a θ =
        kerrDensitizedFthetaPhi Q r a θ) ∧
    sigmaStar
      (kerrResolvingQMinus r a θ)
      (kerrResolvingQPlus r a θ) = 0 ∧
    kerrStationaryNormSq r M a Q θ
      (carterObserver r M a Q θ) = -1 ∧
    kerrRicciNormScalar Q r a θ =
      4 * Q^4 / (Sigma r a θ)^4 ∧
    kerrClockRateFromPrincipalEM Q r a θ =
      Real.sqrt 2 * |Q| / Sigma r a θ ∧
    kerrClockRateFromPrincipalEM Q r a θ * dt =
      Real.sqrt 2 * |Q| * dlam := by
  have hsig0 : Sigma r a θ ≠ 0 := ne_of_gt hsig
  have hdel0 : Delta r M a Q ≠ 0 := ne_of_gt hdel
  have hsin0 : Real.sin θ ≠ 0 := ne_of_gt hsin
  have hfield :=
    kerrPotential_to_CarterPrincipalField
      Q r M a θ hsig hdel
  have hmax :=
    kerrMaxwell_equations_scalar_certificate
      Q r a θ hsig0
  have hdens :=
    kerrDensitizedField_from_metric
      Q r M a θ hsig0 hdel0 hsin0
  exact ⟨hfield.1,
    hmax,
    hdens,
    kerrResolving_balance_rapidity_zero r a θ hsig0,
    carterObserver_unit_timelike r M a Q θ hsig hdel,
    kerrRicciNormScalar_formula Q r a θ hsig0,
    kerrClockRateFromPrincipalEM_formula
      Q r a θ hQ hsig,
    kerrMinoClockFromPrincipalEM
      Q r a θ dt dlam hQ hsig hmino⟩

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


/-! ### Minimal current-first characteristic interface -/

/-- Current-first form of the remaining covariant-phase-space datum.  Here `current`
is already a covector on the characteristic space, exactly as
`X ↦ -(1/2) Ω_can^bulk(X,Y)` in the manuscript.  No parameter response, factorization,
kernel statement, or quotient dimension is supplied independently. -/
structure CharacteristicCurrentData where
  beta : P →ₗ[ℝ] KSpace
  current : KSpace →ₗ[ℝ] ℝ
  positiveWitness : P
  current_positive : 0 < current (beta positiveWitness)

/-- Parameter-space stress response is forced to be the pullback of the characteristic current. -/
def CharacteristicCurrentData.ell
    (D : CharacteristicCurrentData (P:=P) (KSpace:=KSpace)) :
    P →ₗ[ℝ] ℝ :=
  D.current.comp D.beta

/-- The actual characteristic space used by the manuscript is the image of `beta`. -/
def CharacteristicCurrentData.K
    (D : CharacteristicCurrentData (P:=P) (KSpace:=KSpace)) :
    Submodule ℝ KSpace :=
  LinearMap.range D.beta

/-- Restriction of the physical current to the stress-visible characteristic image. -/
def CharacteristicCurrentData.Lambda
    (D : CharacteristicCurrentData (P:=P) (KSpace:=KSpace)) :
    D.K →ₗ[ℝ] ℝ :=
  D.current.domRestrict D.K

/-- The factorization `ell = beta* Lambda` is definitional once the bulk current lives
on characteristic space. -/
theorem characteristicCurrent_factorization
    (D : CharacteristicCurrentData (P:=P) (KSpace:=KSpace)) :
    D.Lambda.comp D.beta.rangeRestrict = D.ell := by
  ext p
  rfl

/-- Parameter directions invisible to the characteristic variation are automatically
invisible to the response. -/
theorem CharacteristicCurrentData.kernel_invisible
    (D : CharacteristicCurrentData (P:=P) (KSpace:=KSpace)) :
    LinearMap.ker D.beta ≤ LinearMap.ker D.ell := by
  intro p hp
  change D.ell p = 0
  simp [CharacteristicCurrentData.ell, hp]

/-- Positivity is inherited by the parameter response without a new hypothesis. -/
theorem CharacteristicCurrentData.ell_positive
    (D : CharacteristicCurrentData (P:=P) (KSpace:=KSpace)) :
    0 < D.ell D.positiveWitness := by
  simpa [CharacteristicCurrentData.ell] using D.current_positive

/-- Therefore the restricted characteristic covector is nonzero. -/
theorem characteristicCurrent_Lambda_nonzero
    (D : CharacteristicCurrentData (P:=P) (KSpace:=KSpace)) :
    D.Lambda ≠ 0 := by
  intro hzero
  have hfac := characteristicCurrent_factorization D
  rw [hzero] at hfac
  have hell : D.ell = 0 := by simpa using hfac.symm
  have hp := D.ell_positive
  rw [hell] at hp
  simp at hp

/-- Surjectivity of `beta.rangeRestrict` makes the current restriction the unique
covector with the required pullback. -/
theorem characteristicCurrent_Lambda_unique
    (D : CharacteristicCurrentData (P:=P) (KSpace:=KSpace))
    (Λ' : D.K →ₗ[ℝ] ℝ)
    (hΛ' : Λ'.comp D.beta.rangeRestrict = D.ell) :
    Λ' = D.Lambda := by
  exact characteristic_range_covector_unique
    D.beta D.ell Λ' D.Lambda hΛ'
    (characteristicCurrent_factorization D)

/-- The stress-visible characteristic quotient is consequently forced to be one real dimension. -/
theorem characteristicCurrent_quotient_finrank_one
    (D : CharacteristicCurrentData (P:=P) (KSpace:=KSpace)) :
    Module.finrank ℝ
      (D.K ⧸ LinearMap.ker D.Lambda) = 1 :=
  clockQuotient_finrank_one D.Lambda
    (characteristicCurrent_Lambda_nonzero D)

/-- Its descended clock covector is therefore canonical and nonzero. -/
noncomputable def CharacteristicCurrentData.clockCovector
    (D : CharacteristicCurrentData (P:=P) (KSpace:=KSpace)) :
    (D.K ⧸ LinearMap.ker D.Lambda) →ₗ[ℝ] ℝ :=
  quotientClockCovector D.Lambda

theorem characteristicCurrent_clockCovector_nonzero
    (D : CharacteristicCurrentData (P:=P) (KSpace:=KSpace)) :
    D.clockCovector ≠ 0 :=
  quotientClockCovector_nonzero D.Lambda
    (characteristicCurrent_Lambda_nonzero D)


/-! ### Construction of the characteristic current from the fixed-point carrier -/

section CarrierCharacteristicConstruction

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Once the compensated Iyer-Wald bulk current is identified with the field-derived
carrier current, the characteristic-current datum is constructed rather than assumed.
The only extra hypothesis here is positivity of one integrated stress test profile. -/
def characteristicCurrentDataOfCarrier
    (beta : P →ₗ[ℝ] KSpace)
    (J T : KSpace →ₗ[ℝ] KSpace)
    (iε : KSpace →ₗ[ℝ] W)
    (integrate : W →ₗ[ℝ] ℝ)
    (hJ : J = (-16 * Real.pi) • T)
    (positiveWitness : P)
    (hpositive :
      0 <
        stressResponse integrate T iε
          (beta positiveWitness)) :
    CharacteristicCurrentData (P:=P) (KSpace:=KSpace) where
  beta := beta
  current := halfCarrierBulkCurrent integrate J iε
  positiveWitness := positiveWitness
  current_positive := by
    rw [halfCarrierBulkCurrent_eq_stressResponse
      integrate J T iε hJ]
    exact hpositive

/-- The current constructed from the carrier is exactly the Maxwell stress response
on characteristic space. -/
theorem characteristicCurrentDataOfCarrier_current
    (beta : P →ₗ[ℝ] KSpace)
    (J T : KSpace →ₗ[ℝ] KSpace)
    (iε : KSpace →ₗ[ℝ] W)
    (integrate : W →ₗ[ℝ] ℝ)
    (hJ : J = (-16 * Real.pi) • T)
    (p0 : P)
    (hpositive :
      0 < stressResponse integrate T iε (beta p0)) :
    (characteristicCurrentDataOfCarrier
      beta J T iε integrate hJ p0 hpositive).current =
      stressResponse integrate T iε := by
  exact halfCarrierBulkCurrent_eq_stressResponse
    integrate J T iε hJ

/-- Consequently its parameter response is literally the pullback of the integrated
stress response along the characteristic map. -/
theorem characteristicCurrentDataOfCarrier_ell
    (beta : P →ₗ[ℝ] KSpace)
    (J T : KSpace →ₗ[ℝ] KSpace)
    (iε : KSpace →ₗ[ℝ] W)
    (integrate : W →ₗ[ℝ] ℝ)
    (hJ : J = (-16 * Real.pi) • T)
    (p0 : P)
    (hpositive :
      0 < stressResponse integrate T iε (beta p0)) :
    (characteristicCurrentDataOfCarrier
      beta J T iε integrate hJ p0 hpositive).ell =
      (stressResponse integrate T iε).comp beta := by
  ext p
  simp [CharacteristicCurrentData.ell,
    characteristicCurrentDataOfCarrier,
    halfCarrierBulkCurrent_eq_stressResponse
      integrate J T iε hJ]

/-- The unique characteristic covector is the restriction of the integrated stress
response to the actual image of the characteristic map. -/
theorem characteristicCurrentDataOfCarrier_Lambda_apply
    (beta : P →ₗ[ℝ] KSpace)
    (J T : KSpace →ₗ[ℝ] KSpace)
    (iε : KSpace →ₗ[ℝ] W)
    (integrate : W →ₗ[ℝ] ℝ)
    (hJ : J = (-16 * Real.pi) • T)
    (p0 : P)
    (hpositive :
      0 < stressResponse integrate T iε (beta p0))
    (X : LinearMap.range beta) :
    (characteristicCurrentDataOfCarrier
      beta J T iε integrate hJ p0 hpositive).Lambda X =
      stressResponse integrate T iε X := by
  change
    halfCarrierBulkCurrent integrate J iε X =
      stressResponse integrate T iε X
  exact LinearMap.congr_fun
    (halfCarrierBulkCurrent_eq_stressResponse
      integrate J T iε hJ) X

end CarrierCharacteristicConstruction

/-! ### Fully field-derived principal characteristic current and positivity -/

/-- Principal Maxwell stress as a genuine linear endomorphism of the tangent model. -/
def principalStressLinear
    (u : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun := principalStressApply u
  map_add' := by
    intro x y
    funext i
    fin_cases i <;>
      simp [principalStressApply, principalStress] <;>
      ring
  map_smul' := by
    intro c x
    funext i
    fin_cases i <;>
      simp [principalStressApply, principalStress] <;>
      ring

/-- Stress endomorphism reconstructed from the explicit principal Maxwell field. -/
def principalStressLinearFromF
    (E B : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
  principalStressLinear (principalFieldEnergyDensity E B)

/-- This linear endomorphism is exactly the matrix obtained from the explicit two-form. -/
theorem principalStressLinearFromF_apply
    (E B : ℝ) (v : Fin 4 → ℝ) (i : Fin 4) :
    principalStressLinearFromF E B v i =
      ∑ j : Fin 4, principalStressFromF E B i j * v j := by
  unfold principalStressLinearFromF principalStressLinear principalStressApply
  apply Finset.sum_congr rfl
  intro j hj
  rw [principalStressFromF_eq_principalStress]

/-- Future-oriented hypersurface contraction in the adapted principal frame. -/
def principalFutureFlux
    (vol : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := -vol * v 0
  map_add' := by
    intro x y
    simp
    ring
  map_smul' := by
    intro c x
    simp
    ring

/-- The unit principal observer sees exactly the Maxwell energy density. -/
theorem principalStressLinearFromF_time_eigen
    (E B : ℝ) :
    principalStressLinearFromF E B principalUhat =
      (-principalFieldEnergyDensity E B) • principalUhat := by
  unfold principalStressLinearFromF principalStressLinear
  simpa [principalUhat] using
    principalStress_time_eigen (principalFieldEnergyDensity E B)

/-- A smeared future principal observer therefore has the exact positive flux
`f ε_EM vol`. -/
theorem principalStressResponse_formula
    (f E B vol : ℝ) :
    stressResponse
        LinearMap.id
        (principalStressLinearFromF E B)
        (principalFutureFlux vol)
        (f • principalUhat) =
      f * principalFieldEnergyDensity E B * vol := by
  change
    principalFutureFlux vol
      (principalStressLinearFromF E B
        (f • principalUhat)) =
      f * principalFieldEnergyDensity E B * vol
  rw [map_smul, principalStressLinearFromF_time_eigen]
  simp [principalFutureFlux, principalUhat, principalBasis]
  ring

/-- Nonzero Maxwell field makes its principal energy density strictly positive. -/
theorem principalFieldEnergyDensity_pos
    (E B : ℝ) (hfield : E ≠ 0 ∨ B ≠ 0) :
    0 < principalFieldEnergyDensity E B := by
  rw [principalFieldEnergyDensity_eq_chi]
  exact div_pos
    (principalChi_pos E B hfield)
    (mul_pos (by norm_num) Real.pi_pos)

/-- Hence positive smearing and positive hypersurface orientation force a positive
integrated stress response directly from the field. -/
theorem principalStressResponse_pos
    (f E B vol : ℝ)
    (hf : 0 < f)
    (hfield : E ≠ 0 ∨ B ≠ 0)
    (hvol : 0 < vol) :
    0 <
      stressResponse
        LinearMap.id
        (principalStressLinearFromF E B)
        (principalFutureFlux vol)
        (f • principalUhat) := by
  rw [principalStressResponse_formula]
  exact mul_pos (mul_pos hf
    (principalFieldEnergyDensity_pos E B hfield)) hvol

section FullyFieldDerivedCharacteristic

variable {P : Type*} [AddCommGroup P] [Module ℝ P]

/-- Data needed only to say which gauge parameter produces a positive multiple of the
already selected principal timelike direction.  No current or positivity statement is input. -/
structure PrincipalCarrierCharacteristicInput where
  beta : P →ₗ[ℝ] (Fin 4 → ℝ)
  positiveWitness : P
  smear : ℝ
  E : ℝ
  B : ℝ
  volume : ℝ
  smear_pos : 0 < smear
  field_nonzero : E ≠ 0 ∨ B ≠ 0
  volume_pos : 0 < volume
  witness_image :
    beta positiveWitness = smear • principalUhat

/-- Field-derived Maxwell stress endomorphism attached to the input. -/
def PrincipalCarrierCharacteristicInput.T
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
  principalStressLinearFromF D.E D.B

/-- Fixed-point jet endomorphism `J=-16πT`, now a definition rather than a premise. -/
def PrincipalCarrierCharacteristicInput.J
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
  (-16 * Real.pi) • D.T

/-- Every matrix coefficient of the characteristic carrier endomorphism is the
fixed-point jet reconstructed directly from the action's metric Euler derivative. -/
theorem PrincipalCarrierCharacteristicInput.J_basis_eq_actionEulerJet
    (D : PrincipalCarrierCharacteristicInput (P:=P))
    (i j : Fin 4) :
    D.J (principalBasis j) i =
      (16 * Real.pi / principalMetricSign i) *
        deriv
          (principalScaledMetricEulerCoeffFromAction
            D.E D.B i j) 0 := by
  rw [← principalJetFromF_forced_from_actionEulerJet D.E D.B i j]
  unfold PrincipalCarrierCharacteristicInput.J
    PrincipalCarrierCharacteristicInput.T
  change
    (-16 * Real.pi) *
      principalStressLinearFromF D.E D.B (principalBasis j) i =
      principalJetFromF D.E D.B i j
  rw [principalStressLinearFromF_apply]
  simp [principalBasis, principalJetFromF]

/-- There is no second linear carrier endomorphism with the same action Euler-jet
matrix coefficients.  The `J` used by the characteristic construction is uniquely
forced by the action derivative. -/
theorem PrincipalCarrierCharacteristicInput.J_unique_from_actionEulerJet
    (D : PrincipalCarrierCharacteristicInput (P:=P))
    (J' : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
    (hJ' : ∀ i j : Fin 4,
      J' (principalBasis j) i =
        (16 * Real.pi / principalMetricSign i) *
          deriv
            (principalScaledMetricEulerCoeffFromAction
              D.E D.B i j) 0) :
    J' = D.J := by
  apply principalLinearMap_ext_on_basis
  intro j
  funext i
  rw [hJ' i j, D.J_basis_eq_actionEulerJet i j]


/-- Future-oriented contraction with the chosen positive hypersurface density. -/
def PrincipalCarrierCharacteristicInput.iε
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  principalFutureFlux D.volume

/-- The distinguished parameter has strictly positive integrated stress response,
derived entirely from the explicit Maxwell field and orientation data. -/
theorem PrincipalCarrierCharacteristicInput.response_positive
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    0 <
      stressResponse
        LinearMap.id D.T D.iε
        (D.beta D.positiveWitness) := by
  rw [D.witness_image]
  exact principalStressResponse_pos
    D.smear D.E D.B D.volume
    D.smear_pos D.field_nonzero D.volume_pos

/-- The characteristic-current datum is now constructed from the explicit Maxwell field,
the fixed-point jet relation, and the characteristic map. -/
def PrincipalCarrierCharacteristicInput.toCharacteristicCurrentData
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    CharacteristicCurrentData
      (P:=P) (KSpace:=(Fin 4 → ℝ)) :=
  characteristicCurrentDataOfCarrier
    D.beta D.J D.T D.iε LinearMap.id
    rfl D.positiveWitness D.response_positive

/-- Its current is exactly the integrated Maxwell stress response. -/
theorem principalCarrierCharacteristic_current
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    D.toCharacteristicCurrentData.current =
      stressResponse LinearMap.id D.T D.iε := by
  exact characteristicCurrentDataOfCarrier_current
    D.beta D.J D.T D.iε LinearMap.id
    rfl D.positiveWitness D.response_positive

/-- Its characteristic covector is forced and nonzero. -/
theorem principalCarrierCharacteristic_Lambda_nonzero
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    D.toCharacteristicCurrentData.Lambda ≠ 0 :=
  characteristicCurrent_Lambda_nonzero
    D.toCharacteristicCurrentData

/-- The resulting stress-visible characteristic quotient is therefore exactly one-dimensional. -/
theorem principalCarrierCharacteristic_quotient_finrank_one
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    Module.finrank ℝ
      (D.toCharacteristicCurrentData.K ⧸
        LinearMap.ker D.toCharacteristicCurrentData.Lambda) = 1 :=
  characteristicCurrent_quotient_finrank_one
    D.toCharacteristicCurrentData

/-- The descended clock covector is canonical and nonzero, with no independently supplied
response or normalization. -/
theorem principalCarrierCharacteristic_clock_nonzero
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    D.toCharacteristicCurrentData.clockCovector ≠ 0 :=
  characteristicCurrent_clockCovector_nonzero
    D.toCharacteristicCurrentData

/-- Unique global-to-local clock equivalence for the fully field-derived characteristic datum. -/
noncomputable def PrincipalCarrierCharacteristicInput.globalLocalClockEquiv
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    (D.toCharacteristicCurrentData.K ⧸
        LinearMap.ker D.toCharacteristicCurrentData.Lambda) ≃ₗ[ℝ]
      ((Fin 4 → ℝ) ⧸ LinearMap.ker principalTOLinear) :=
  globalToPrincipalLocalClockEquiv
    D.toCharacteristicCurrentData.Lambda
    (principalCarrierCharacteristic_Lambda_nonzero D)

/-- The local clock covector pulls back exactly to the field-derived global clock covector. -/
theorem principalCarrierCharacteristic_globalLocal_pullback
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    (quotientClockCovector principalTOLinear).comp
      (globalToPrincipalLocalClockMap
        D.toCharacteristicCurrentData.Lambda) =
      D.toCharacteristicCurrentData.clockCovector := by
  exact globalToPrincipalLocalClockMap_pullback
    D.toCharacteristicCurrentData.Lambda

/-- The globally normalized field-derived clock unit maps to the local principal clock unit. -/
theorem principalCarrierCharacteristic_globalUnit_maps_local
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    globalToPrincipalLocalClockMap
      D.toCharacteristicCurrentData.Lambda
      (globalClockQuotientUnit
        D.toCharacteristicCurrentData.Lambda
        (principalCarrierCharacteristic_Lambda_nonzero D)) =
      principalLocalQuotientUnit := by
  exact globalClockUnit_maps_to_principalUnit
    D.toCharacteristicCurrentData.Lambda
    (principalCarrierCharacteristic_Lambda_nonzero D)

/-- Composing with the canonical local lift sends that same global unit all the way to
the uniquely normalized principal timelike vector. -/
theorem principalCarrierCharacteristic_normalizationBridge
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    principalLocalLift
      (globalToPrincipalLocalClockMap
        D.toCharacteristicCurrentData.Lambda
        (globalClockQuotientUnit
          D.toCharacteristicCurrentData.Lambda
          (principalCarrierCharacteristic_Lambda_nonzero D))) =
      principalUhat := by
  exact normalizationBridge_principal
    D.toCharacteristicCurrentData.Lambda
    (principalCarrierCharacteristic_Lambda_nonzero D)

/-- End-to-end algebraic certificate for the manuscript's characteristic clock chain:
field-derived nonvanishing, forced one-dimensional quotient, exact covector-preserving
global/local identification, and normalization on `û_*`. -/
theorem principalCarrierCharacteristic_clock_chain
    (D : PrincipalCarrierCharacteristicInput (P:=P)) :
    D.toCharacteristicCurrentData.Lambda ≠ 0 ∧
    Module.finrank ℝ
      (D.toCharacteristicCurrentData.K ⧸
        LinearMap.ker D.toCharacteristicCurrentData.Lambda) = 1 ∧
    (quotientClockCovector principalTOLinear).comp
      (globalToPrincipalLocalClockMap
        D.toCharacteristicCurrentData.Lambda) =
      D.toCharacteristicCurrentData.clockCovector ∧
    principalLocalLift
      (globalToPrincipalLocalClockMap
        D.toCharacteristicCurrentData.Lambda
        (globalClockQuotientUnit
          D.toCharacteristicCurrentData.Lambda
          (principalCarrierCharacteristic_Lambda_nonzero D))) =
      principalUhat := by
  exact ⟨principalCarrierCharacteristic_Lambda_nonzero D,
    principalCarrierCharacteristic_quotient_finrank_one D,
    principalCarrierCharacteristic_globalLocal_pullback D,
    principalCarrierCharacteristic_normalizationBridge D⟩


/-- Strongest single theorem currently available for the field-derived core:
the nonzero Maxwell field fixes the unique relative solution point, its first normal
derivative is the field jet, that jet obeys Rainich, all intrinsic clock rates coincide,
and the characteristic clock descends uniquely to the normalized principal timelike line. -/
theorem principalField_forced_core_chain
    (D : PrincipalCarrierCharacteristicInput (P:=P))
    (u s : ℝ) :
    ((8 * Real.pi * principalFieldEnergyDensity D.E D.B =
        8 * Real.pi *
          maxwellStressScaleFactor (rhoUS u s) (lambdaUS u s) *
          principalFieldEnergyDensity D.E D.B) ↔
        s = 0) ∧
    deriv (principalScaledResidualFromF D.E D.B 0 0) 0 =
      principalJetFromF D.E D.B 0 0 ∧
    (∀ i j : Fin 4,
      (∑ k : Fin 4,
        principalJetFromF D.E D.B i k *
          principalJetFromF D.E D.B k j) =
        (principalChi D.E D.B)^2 *
          (if i = j then 1 else 0)) ∧
    (principalClockRate D.E D.B =
        4 * Real.sqrt
          (Real.pi * principalFieldEnergyDensity D.E D.B) ∧
     principalClockRate D.E D.B =
        Real.sqrt
          (Real.sqrt
            ((maxwellI D.E D.B)^2 +
              (maxwellJ D.E D.B)^2)) ∧
     principalClockRate D.E D.B =
        Real.sqrt
          (Real.sqrt
            (principalRicciNormFromCarrier
              (principalChi D.E D.B)))) ∧
    (D.toCharacteristicCurrentData.Lambda ≠ 0 ∧
     Module.finrank ℝ
       (D.toCharacteristicCurrentData.K ⧸
         LinearMap.ker D.toCharacteristicCurrentData.Lambda) = 1 ∧
     (quotientClockCovector principalTOLinear).comp
       (globalToPrincipalLocalClockMap
         D.toCharacteristicCurrentData.Lambda) =
       D.toCharacteristicCurrentData.clockCovector ∧
     principalLocalLift
       (globalToPrincipalLocalClockMap
         D.toCharacteristicCurrentData.Lambda
         (globalClockQuotientUnit
           D.toCharacteristicCurrentData.Lambda
           (principalCarrierCharacteristic_Lambda_nonzero D))) =
       principalUhat) := by
  refine ⟨principalField_solution_preserving_iff
      u s D.E D.B D.field_nonzero,
    principalScaledResidualFromF_deriv_zero D.E D.B 0 0,
    ?_,
    principalClockRate_three_way D.E D.B,
    principalCarrierCharacteristic_clock_chain D⟩
  intro i j
  exact principalJetFromF_rainich D.E D.B i j


/-! ### Lagrangian-backed characteristic clock: covariant phase space to the normalized line -/

section LagrangianBackedCharacteristic

variable {L : Type*} [AddCommGroup L] [Module ℝ L]

/-- Strongest current interface in the file: the explicit principal Maxwell field
constructs the stress/carrier current, while a single Lagrangian-level Iyer-Wald
operator identity identifies that current with the covariant-phase-space descendant
of the reciprocal Einstein-Maxwell Lagrangian normal jet. -/
structure PrincipalLagrangianCharacteristicInput where
  carrier : PrincipalCarrierCharacteristicInput (P:=P)
  LG : L
  LM : L
  iw : LagrangianIyerWaldOperators
    (L:=L) (C:=((Fin 4 → ℝ) →ₗ[ℝ] ℝ))
  constraintGravity :
    iw.constraint LG =
      stressResponse LinearMap.id carrier.T carrier.iε
  constraintMaxwell :
    iw.constraint LM =
      -(stressResponse LinearMap.id carrier.T carrier.iε)

/-- The relative-normal Lagrangian direction itself. -/
def PrincipalLagrangianCharacteristicInput.relativeNormalJet
    (D : PrincipalLagrangianCharacteristicInput (P:=P) (L:=L)) : L :=
  reciprocalLagrangianNormalJet D.LG D.LM

/-- Characteristic current constructed directly from the Lagrangian Iyer-Wald
descendant, with the universal negative-half normalization. -/
def PrincipalLagrangianCharacteristicInput.iwCharacteristicCurrent
    (D : PrincipalLagrangianCharacteristicInput (P:=P) (L:=L)) :
    (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  (-1 / 2 : ℝ) •
    (D.iw.omegaXY D.relativeNormalJet +
      D.iw.dB D.relativeNormalJet)

/-- The Lagrangian Iyer-Wald current is exactly the explicit Maxwell stress response. -/
theorem principalLagrangianCharacteristic_iwCurrent_eq_stress
    (D : PrincipalLagrangianCharacteristicInput (P:=P) (L:=L)) :
    D.iwCharacteristicCurrent =
      stressResponse LinearMap.id D.carrier.T D.carrier.iε := by
  unfold PrincipalLagrangianCharacteristicInput.iwCharacteristicCurrent
    PrincipalLagrangianCharacteristicInput.relativeNormalJet
  exact lagrangianIyerWald_half_compensated_eq_stressResponse
    D.iw D.LG D.LM LinearMap.id
    D.carrier.J D.carrier.T D.carrier.iε rfl
    D.constraintGravity D.constraintMaxwell

/-- Hence the current obtained from the Lagrangian covariant-phase-space identity
coincides exactly with the current used to construct the characteristic quotient. -/
theorem principalLagrangianCharacteristic_iwCurrent_eq_characteristicCurrent
    (D : PrincipalLagrangianCharacteristicInput (P:=P) (L:=L)) :
    D.iwCharacteristicCurrent =
      D.carrier.toCharacteristicCurrentData.current := by
  rw [principalLagrangianCharacteristic_iwCurrent_eq_stress D,
    principalCarrierCharacteristic_current D.carrier]

/-- The covariant-phase-space current is nonzero because its Lagrangian descendant
is the positive Maxwell stress current on the distinguished future test profile. -/
theorem principalLagrangianCharacteristic_iwCurrent_nonzero
    (D : PrincipalLagrangianCharacteristicInput (P:=P) (L:=L)) :
    D.iwCharacteristicCurrent ≠ 0 := by
  rw [principalLagrangianCharacteristic_iwCurrent_eq_characteristicCurrent D]
  intro hzero
  have hcur : D.carrier.toCharacteristicCurrentData.current = 0 := hzero
  have hp := D.carrier.toCharacteristicCurrentData.current_positive
  rw [hcur] at hp
  simp at hp

/-- End-to-end Lagrangian-backed clock certificate: the unique compensated
Iyer-Wald descendant equals the explicit Maxwell current, and the entire already-proved
one-dimensional clock/normalization chain follows from that same current. -/
theorem principalLagrangianCharacteristic_clock_chain
    (D : PrincipalLagrangianCharacteristicInput (P:=P) (L:=L)) :
    D.iwCharacteristicCurrent =
        D.carrier.toCharacteristicCurrentData.current ∧
    D.carrier.toCharacteristicCurrentData.Lambda ≠ 0 ∧
    Module.finrank ℝ
      (D.carrier.toCharacteristicCurrentData.K ⧸
        LinearMap.ker D.carrier.toCharacteristicCurrentData.Lambda) = 1 ∧
    (quotientClockCovector principalTOLinear).comp
      (globalToPrincipalLocalClockMap
        D.carrier.toCharacteristicCurrentData.Lambda) =
      D.carrier.toCharacteristicCurrentData.clockCovector ∧
    principalLocalLift
      (globalToPrincipalLocalClockMap
        D.carrier.toCharacteristicCurrentData.Lambda
        (globalClockQuotientUnit
          D.carrier.toCharacteristicCurrentData.Lambda
          (principalCarrierCharacteristic_Lambda_nonzero D.carrier))) =
      principalUhat := by
  rcases principalCarrierCharacteristic_clock_chain D.carrier with
    ⟨hL, hdim, hpull, hnorm⟩
  exact ⟨
    principalLagrangianCharacteristic_iwCurrent_eq_characteristicCurrent D,
    hL, hdim, hpull, hnorm⟩

/-! ### Lagrangian-first-variation-backed clock: deltaL to normalized clock line -/

/-- Strongest covariant-phase-space input in the file. The primitive datum contains
the actual first-variation equation `deltaL = E deltaPhi + dTheta`; Iyer-Wald is a
derived theorem. -/
structure PrincipalLagrangianVariationCharacteristicInput where
  carrier : PrincipalCarrierCharacteristicInput (P:=P)
  LG : L
  LM : L
  variation : LagrangianVariationNoetherOperators
    (L:=L) (C:=((Fin 4 → ℝ) →ₗ[ℝ] ℝ))
  constraintGravity :
    variation.constraint LG =
      stressResponse LinearMap.id carrier.T carrier.iε
  constraintMaxwell :
    variation.constraint LM =
      -(stressResponse LinearMap.id carrier.T carrier.iε)

def PrincipalLagrangianVariationCharacteristicInput.relativeNormalJet
    (D : PrincipalLagrangianVariationCharacteristicInput (P:=P) (L:=L)) : L :=
  reciprocalLagrangianNormalJet D.LG D.LM

def PrincipalLagrangianVariationCharacteristicInput.characteristicCurrent
    (D : PrincipalLagrangianVariationCharacteristicInput (P:=P) (L:=L)) :
    (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  (-1 / 2 : ℝ) •
    (D.variation.omegaXY D.relativeNormalJet +
      D.variation.dB D.relativeNormalJet)

/-- The first-variation-derived current equals the explicit Maxwell stress response. -/
theorem principalLagrangianVariation_current_eq_stress
    (D : PrincipalLagrangianVariationCharacteristicInput (P:=P) (L:=L)) :
    D.characteristicCurrent =
      stressResponse LinearMap.id D.carrier.T D.carrier.iε := by
  unfold PrincipalLagrangianVariationCharacteristicInput.characteristicCurrent
    PrincipalLagrangianVariationCharacteristicInput.relativeNormalJet
  exact lagrangianVariation_half_compensated_eq_stressResponse
    D.variation D.LG D.LM LinearMap.id
    D.carrier.J D.carrier.T D.carrier.iε rfl
    D.constraintGravity D.constraintMaxwell

/-- Hence the current is exactly the one that defines the characteristic quotient. -/
theorem principalLagrangianVariation_current_eq_characteristicCurrent
    (D : PrincipalLagrangianVariationCharacteristicInput (P:=P) (L:=L)) :
    D.characteristicCurrent =
      D.carrier.toCharacteristicCurrentData.current := by
  rw [principalLagrangianVariation_current_eq_stress D,
    principalCarrierCharacteristic_current D.carrier]

/-- Positivity of the field-derived Maxwell response makes this derived current nonzero. -/
theorem principalLagrangianVariation_current_nonzero
    (D : PrincipalLagrangianVariationCharacteristicInput (P:=P) (L:=L)) :
    D.characteristicCurrent ≠ 0 := by
  rw [principalLagrangianVariation_current_eq_characteristicCurrent D]
  intro hzero
  have hp := D.carrier.toCharacteristicCurrentData.current_positive
  rw [hzero] at hp
  simp at hp

/-- End-to-end clock theorem sourced at the actual Lagrangian first variation. -/
theorem principalLagrangianVariation_clock_chain
    (D : PrincipalLagrangianVariationCharacteristicInput (P:=P) (L:=L)) :
    D.characteristicCurrent =
        D.carrier.toCharacteristicCurrentData.current ∧
    D.carrier.toCharacteristicCurrentData.Lambda ≠ 0 ∧
    Module.finrank ℝ
      (D.carrier.toCharacteristicCurrentData.K ⧸
        LinearMap.ker D.carrier.toCharacteristicCurrentData.Lambda) = 1 ∧
    (quotientClockCovector principalTOLinear).comp
      (globalToPrincipalLocalClockMap
        D.carrier.toCharacteristicCurrentData.Lambda) =
      D.carrier.toCharacteristicCurrentData.clockCovector ∧
    principalLocalLift
      (globalToPrincipalLocalClockMap
        D.carrier.toCharacteristicCurrentData.Lambda
        (globalClockQuotientUnit
          D.carrier.toCharacteristicCurrentData.Lambda
          (principalCarrierCharacteristic_Lambda_nonzero D.carrier))) =
      principalUhat := by
  rcases principalCarrierCharacteristic_clock_chain D.carrier with
    ⟨hL, hdim, hpull, hnorm⟩
  exact ⟨principalLagrangianVariation_current_eq_characteristicCurrent D,
    hL, hdim, hpull, hnorm⟩

/-- Strongest forced-core theorem: the explicit Maxwell field fixes relative rest,
the surviving carrier jet and Rainich involution; the actual Lagrangian first
variation derives the compensated covariant-phase-space current; and that current
forces the one-dimensional normalized clock line. -/
theorem principalLagrangianVariation_forced_core_chain
    (D : PrincipalLagrangianVariationCharacteristicInput (P:=P) (L:=L))
    (u s : ℝ) :
    ((8 * Real.pi * principalFieldEnergyDensity D.carrier.E D.carrier.B =
        8 * Real.pi *
          maxwellStressScaleFactor (rhoUS u s) (lambdaUS u s) *
          principalFieldEnergyDensity D.carrier.E D.carrier.B) ↔ s = 0) ∧
    deriv (principalScaledResidualFromF
      D.carrier.E D.carrier.B 0 0) 0 =
      principalJetFromF D.carrier.E D.carrier.B 0 0 ∧
    (∀ i j : Fin 4,
      (∑ k : Fin 4,
        principalJetFromF D.carrier.E D.carrier.B i k *
          principalJetFromF D.carrier.E D.carrier.B k j) =
        (principalChi D.carrier.E D.carrier.B)^2 *
          (if i = j then 1 else 0)) ∧
    D.characteristicCurrent =
      D.carrier.toCharacteristicCurrentData.current ∧
    D.carrier.toCharacteristicCurrentData.Lambda ≠ 0 ∧
    Module.finrank ℝ
      (D.carrier.toCharacteristicCurrentData.K ⧸
        LinearMap.ker D.carrier.toCharacteristicCurrentData.Lambda) = 1 ∧
    principalLocalLift
      (globalToPrincipalLocalClockMap
        D.carrier.toCharacteristicCurrentData.Lambda
        (globalClockQuotientUnit
          D.carrier.toCharacteristicCurrentData.Lambda
          (principalCarrierCharacteristic_Lambda_nonzero D.carrier))) =
      principalUhat := by
  rcases principalField_forced_core_chain D.carrier u s with
    ⟨hrest, hjet, hrainich, _hrates, hclock⟩
  rcases hclock with ⟨hL, hdim, _hpull, hnorm⟩
  exact ⟨hrest, hjet, hrainich,
    principalLagrangianVariation_current_eq_characteristicCurrent D,
    hL, hdim, hnorm⟩

/-! ### First-variation-backed characteristic clock: no primitive Iyer-Wald identity -/

/-- Stronger covariant-phase-space input.  The Iyer-Wald operator identity is not
supplied: it is derived from the first-variation/Cartan/Noether data in `variation`. -/
structure PrincipalFirstVariationCharacteristicInput where
  carrier : PrincipalCarrierCharacteristicInput (P:=P)
  LG : L
  LM : L
  variation : FirstVariationNoetherOperators
    (L:=L) (C:=((Fin 4 → ℝ) →ₗ[ℝ] ℝ))
  constraintGravity :
    variation.constraint LG =
      stressResponse LinearMap.id carrier.T carrier.iε
  constraintMaxwell :
    variation.constraint LM =
      -(stressResponse LinearMap.id carrier.T carrier.iε)

/-- The older Lagrangian/Iyer-Wald package is reconstructed canonically from the
first-variation data. -/
def PrincipalFirstVariationCharacteristicInput.toLagrangianInput
    (D : PrincipalFirstVariationCharacteristicInput (P:=P) (L:=L)) :
    PrincipalLagrangianCharacteristicInput (P:=P) (L:=L) where
  carrier := D.carrier
  LG := D.LG
  LM := D.LM
  iw := D.variation.toLagrangianIyerWaldOperators
  constraintGravity := by
    simpa [FirstVariationNoetherOperators.toLagrangianIyerWaldOperators] using
      D.constraintGravity
  constraintMaxwell := by
    simpa [FirstVariationNoetherOperators.toLagrangianIyerWaldOperators] using
      D.constraintMaxwell

/-- Characteristic current obtained directly from the first-variation-derived
covariant-phase-space operator. -/
def PrincipalFirstVariationCharacteristicInput.characteristicCurrent
    (D : PrincipalFirstVariationCharacteristicInput (P:=P) (L:=L)) :
    (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  D.toLagrangianInput.iwCharacteristicCurrent

/-- The current is forced to be the explicit Maxwell stress response without an
independent Iyer-Wald identity hypothesis. -/
theorem principalFirstVariationCharacteristic_current_eq_stress
    (D : PrincipalFirstVariationCharacteristicInput (P:=P) (L:=L)) :
    D.characteristicCurrent =
      stressResponse LinearMap.id D.carrier.T D.carrier.iε := by
  exact principalLagrangianCharacteristic_iwCurrent_eq_stress
    D.toLagrangianInput

/-- Hence it is exactly the field-derived current defining the characteristic
quotient and clock covector. -/
theorem principalFirstVariationCharacteristic_current_eq_characteristicCurrent
    (D : PrincipalFirstVariationCharacteristicInput (P:=P) (L:=L)) :
    D.characteristicCurrent =
      D.carrier.toCharacteristicCurrentData.current := by
  exact principalLagrangianCharacteristic_iwCurrent_eq_characteristicCurrent
    D.toLagrangianInput

/-- The derived current is nonzero by the explicit Maxwell positivity witness. -/
theorem principalFirstVariationCharacteristic_current_nonzero
    (D : PrincipalFirstVariationCharacteristicInput (P:=P) (L:=L)) :
    D.characteristicCurrent ≠ 0 := by
  exact principalLagrangianCharacteristic_iwCurrent_nonzero
    D.toLagrangianInput

/-- End-to-end covariant-phase-space clock certificate sourced one logical layer
earlier than Iyer-Wald: first variation + Cartan + Noether decomposition imply the
unique compensated current, which equals the Maxwell current and forces the same
one-dimensional normalized clock line. -/
theorem principalFirstVariationCharacteristic_clock_chain
    (D : PrincipalFirstVariationCharacteristicInput (P:=P) (L:=L)) :
    D.characteristicCurrent =
        D.carrier.toCharacteristicCurrentData.current ∧
    D.carrier.toCharacteristicCurrentData.Lambda ≠ 0 ∧
    Module.finrank ℝ
      (D.carrier.toCharacteristicCurrentData.K ⧸
        LinearMap.ker D.carrier.toCharacteristicCurrentData.Lambda) = 1 ∧
    (quotientClockCovector principalTOLinear).comp
      (globalToPrincipalLocalClockMap
        D.carrier.toCharacteristicCurrentData.Lambda) =
      D.carrier.toCharacteristicCurrentData.clockCovector ∧
    principalLocalLift
      (globalToPrincipalLocalClockMap
        D.carrier.toCharacteristicCurrentData.Lambda
        (globalClockQuotientUnit
          D.carrier.toCharacteristicCurrentData.Lambda
          (principalCarrierCharacteristic_Lambda_nonzero D.carrier))) =
      principalUhat := by
  exact principalLagrangianCharacteristic_clock_chain
    D.toLagrangianInput

/-- Strongest combined field/current statement with no primitive Iyer-Wald identity:
the Maxwell field fixes the relative solution, carrier, Rainich structure, clock rate,
and the first-variation-derived characteristic current fixes the normalized clock line. -/
theorem principalFirstVariation_forced_core_chain
    (D : PrincipalFirstVariationCharacteristicInput (P:=P) (L:=L))
    (u s : ℝ) :
    ((8 * Real.pi * principalFieldEnergyDensity D.carrier.E D.carrier.B =
        8 * Real.pi *
          maxwellStressScaleFactor (rhoUS u s) (lambdaUS u s) *
          principalFieldEnergyDensity D.carrier.E D.carrier.B) ↔ s = 0) ∧
    deriv (principalScaledResidualFromF
      D.carrier.E D.carrier.B 0 0) 0 =
      principalJetFromF D.carrier.E D.carrier.B 0 0 ∧
    (∀ i j : Fin 4,
      (∑ k : Fin 4,
        principalJetFromF D.carrier.E D.carrier.B i k *
          principalJetFromF D.carrier.E D.carrier.B k j) =
        (principalChi D.carrier.E D.carrier.B)^2 *
          (if i = j then 1 else 0)) ∧
    D.characteristicCurrent =
      D.carrier.toCharacteristicCurrentData.current ∧
    D.carrier.toCharacteristicCurrentData.Lambda ≠ 0 ∧
    Module.finrank ℝ
      (D.carrier.toCharacteristicCurrentData.K ⧸
        LinearMap.ker D.carrier.toCharacteristicCurrentData.Lambda) = 1 ∧
    principalLocalLift
      (globalToPrincipalLocalClockMap
        D.carrier.toCharacteristicCurrentData.Lambda
        (globalClockQuotientUnit
          D.carrier.toCharacteristicCurrentData.Lambda
          (principalCarrierCharacteristic_Lambda_nonzero D.carrier))) =
      principalUhat := by
  rcases principalField_forced_core_chain D.carrier u s with
    ⟨hrest, hjet, hrainich, _hrates, hclock⟩
  rcases hclock with ⟨hL, hdim, _hpull, hnorm⟩
  exact ⟨hrest, hjet, hrainich,
    principalFirstVariationCharacteristic_current_eq_characteristicCurrent D,
    hL, hdim, hnorm⟩

/-! ### Primitive-Noether-backed clock: no first-variation identities as input -/

/-- Strongest covariant-phase-space interface in this file.  Only the primitive
Noether descendants and their gravity/Maxwell constraint values are supplied.
The first-variation identities, Iyer-Wald identity, compensated current, and
clock quotient are all reconstructed below. -/
structure PrincipalPrimitiveNoetherCharacteristicInput where
  carrier : PrincipalCarrierCharacteristicInput (P:=P)
  LG : L
  LM : L
  primitive : PrimitiveNoetherOperators
    (L:=L) (C:=((Fin 4 → ℝ) →ₗ[ℝ] ℝ))
  constraintGravity :
    primitive.toFirstVariationNoetherOperators.constraint LG =
      stressResponse LinearMap.id carrier.T carrier.iε
  constraintMaxwell :
    primitive.toFirstVariationNoetherOperators.constraint LM =
      -(stressResponse LinearMap.id carrier.T carrier.iε)

/-- Canonical promotion to the first-variation-backed interface. -/
def PrincipalPrimitiveNoetherCharacteristicInput.toFirstVariationInput
    (D : PrincipalPrimitiveNoetherCharacteristicInput (P:=P) (L:=L)) :
    PrincipalFirstVariationCharacteristicInput (P:=P) (L:=L) where
  carrier := D.carrier
  LG := D.LG
  LM := D.LM
  variation := D.primitive.toFirstVariationNoetherOperators
  constraintGravity := D.constraintGravity
  constraintMaxwell := D.constraintMaxwell

/-- Primitive Noether data therefore determines the same unique characteristic current. -/
def PrincipalPrimitiveNoetherCharacteristicInput.characteristicCurrent
    (D : PrincipalPrimitiveNoetherCharacteristicInput (P:=P) (L:=L)) :
    (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  D.toFirstVariationInput.characteristicCurrent

theorem principalPrimitiveNoetherCharacteristic_current_eq_characteristicCurrent
    (D : PrincipalPrimitiveNoetherCharacteristicInput (P:=P) (L:=L)) :
    D.characteristicCurrent =
      D.carrier.toCharacteristicCurrentData.current := by
  exact principalFirstVariationCharacteristic_current_eq_characteristicCurrent
    D.toFirstVariationInput

/-- The full normalized clock chain now follows without supplying any
first-variation, Cartan, Noether-decomposition, or Iyer-Wald identity premise. -/
theorem principalPrimitiveNoetherCharacteristic_clock_chain
    (D : PrincipalPrimitiveNoetherCharacteristicInput (P:=P) (L:=L)) :
    D.characteristicCurrent =
        D.carrier.toCharacteristicCurrentData.current ∧
    D.carrier.toCharacteristicCurrentData.Lambda ≠ 0 ∧
    Module.finrank ℝ
      (D.carrier.toCharacteristicCurrentData.K ⧸
        LinearMap.ker D.carrier.toCharacteristicCurrentData.Lambda) = 1 ∧
    (quotientClockCovector principalTOLinear).comp
      (globalToPrincipalLocalClockMap
        D.carrier.toCharacteristicCurrentData.Lambda) =
      D.carrier.toCharacteristicCurrentData.clockCovector ∧
    principalLocalLift
      (globalToPrincipalLocalClockMap
        D.carrier.toCharacteristicCurrentData.Lambda
        (globalClockQuotientUnit
          D.carrier.toCharacteristicCurrentData.Lambda
          (principalCarrierCharacteristic_Lambda_nonzero D.carrier))) =
      principalUhat := by
  exact principalFirstVariationCharacteristic_clock_chain
    D.toFirstVariationInput

/-- Strongest algebraic field/current core: the relative fixed point, action-derived
carrier, Rainich square, primitive-Noether current, one-dimensional quotient, and
normalized clock line are all forced in one implication chain. -/
theorem principalPrimitiveNoether_forced_core_chain
    (D : PrincipalPrimitiveNoetherCharacteristicInput (P:=P) (L:=L))
    (u s : ℝ) :
    ((8 * Real.pi * principalFieldEnergyDensity D.carrier.E D.carrier.B =
        8 * Real.pi *
          maxwellStressScaleFactor (rhoUS u s) (lambdaUS u s) *
          principalFieldEnergyDensity D.carrier.E D.carrier.B) ↔ s = 0) ∧
    deriv (principalScaledResidualFromF
      D.carrier.E D.carrier.B 0 0) 0 =
      principalJetFromF D.carrier.E D.carrier.B 0 0 ∧
    (∀ i j : Fin 4,
      D.carrier.J (principalBasis j) i =
        (16 * Real.pi / principalMetricSign i) *
          deriv
            (principalScaledMetricEulerCoeffFromAction
              D.carrier.E D.carrier.B i j) 0) ∧
    (∀ i j : Fin 4,
      (∑ k : Fin 4,
        principalJetFromF D.carrier.E D.carrier.B i k *
          principalJetFromF D.carrier.E D.carrier.B k j) =
        (principalChi D.carrier.E D.carrier.B)^2 *
          (if i = j then 1 else 0)) ∧
    D.characteristicCurrent =
      D.carrier.toCharacteristicCurrentData.current ∧
    D.carrier.toCharacteristicCurrentData.Lambda ≠ 0 ∧
    Module.finrank ℝ
      (D.carrier.toCharacteristicCurrentData.K ⧸
        LinearMap.ker D.carrier.toCharacteristicCurrentData.Lambda) = 1 ∧
    principalLocalLift
      (globalToPrincipalLocalClockMap
        D.carrier.toCharacteristicCurrentData.Lambda
        (globalClockQuotientUnit
          D.carrier.toCharacteristicCurrentData.Lambda
          (principalCarrierCharacteristic_Lambda_nonzero D.carrier))) =
      principalUhat := by
  rcases principalFirstVariation_forced_core_chain
      D.toFirstVariationInput u s with
    ⟨hrest, hjet, hrainich, hcur, hL, hdim, hnorm⟩
  refine ⟨hrest, hjet, ?_, hrainich, hcur, hL, hdim, hnorm⟩
  intro i j
  exact D.carrier.J_basis_eq_actionEulerJet i j

end LagrangianBackedCharacteristic

end FullyFieldDerivedCharacteristic

/-! ### Maxwell field-derived positivity for a current-first interface -/

/-- Strong current-first Maxwell interface.  The current is the only covariant-phase-space
object supplied; its nonvanishing is forced by one explicit principal-field test value. -/
structure PrincipalFieldCurrentData where
  beta : P →ₗ[ℝ] KSpace
  current : KSpace →ₗ[ℝ] ℝ
  positiveWitness : P
  smear : ℝ
  E : ℝ
  B : ℝ
  volume : ℝ
  smear_pos : 0 < smear
  field_nonzero : E ≠ 0 ∨ B ≠ 0
  volume_pos : 0 < volume
  current_formula :
    current (beta positiveWitness) =
      maxwellPositiveResponseFromField smear E B volume

/-- Maxwell positivity makes the supplied physical current positive on the test profile. -/
theorem PrincipalFieldCurrentData.current_positive
    (D : PrincipalFieldCurrentData (P:=P) (KSpace:=KSpace)) :
    0 < D.current (D.beta D.positiveWitness) := by
  rw [D.current_formula]
  exact maxwellPositiveResponseFromField_pos
    D.smear D.E D.B D.volume
    D.smear_pos D.field_nonzero D.volume_pos

/-- Therefore the strong Maxwell data canonically gives the minimal current-first datum. -/
def PrincipalFieldCurrentData.toCharacteristicCurrentData
    (D : PrincipalFieldCurrentData (P:=P) (KSpace:=KSpace)) :
    CharacteristicCurrentData (P:=P) (KSpace:=KSpace) where
  beta := D.beta
  current := D.current
  positiveWitness := D.positiveWitness
  current_positive := D.current_positive

/-- Its parameter response is not input data; it is the pullback of the physical current. -/
def PrincipalFieldCurrentData.ell
    (D : PrincipalFieldCurrentData (P:=P) (KSpace:=KSpace)) :
    P →ₗ[ℝ] ℝ :=
  D.toCharacteristicCurrentData.ell

/-- The characteristic covector is likewise the forced restriction of the physical current. -/
def PrincipalFieldCurrentData.Lambda
    (D : PrincipalFieldCurrentData (P:=P) (KSpace:=KSpace)) :
    LinearMap.range D.beta →ₗ[ℝ] ℝ :=
  D.toCharacteristicCurrentData.Lambda

theorem principalFieldCurrent_factorization
    (D : PrincipalFieldCurrentData (P:=P) (KSpace:=KSpace)) :
    D.Lambda.comp D.beta.rangeRestrict = D.ell :=
  characteristicCurrent_factorization D.toCharacteristicCurrentData

theorem principalFieldCurrent_Lambda_nonzero
    (D : PrincipalFieldCurrentData (P:=P) (KSpace:=KSpace)) :
    D.Lambda ≠ 0 :=
  characteristicCurrent_Lambda_nonzero D.toCharacteristicCurrentData

theorem principalFieldCurrent_Lambda_unique
    (D : PrincipalFieldCurrentData (P:=P) (KSpace:=KSpace))
    (Λ' : LinearMap.range D.beta →ₗ[ℝ] ℝ)
    (hΛ' : Λ'.comp D.beta.rangeRestrict = D.ell) :
    Λ' = D.Lambda :=
  characteristicCurrent_Lambda_unique
    D.toCharacteristicCurrentData Λ' hΛ'

theorem principalFieldCurrent_quotient_finrank_one
    (D : PrincipalFieldCurrentData (P:=P) (KSpace:=KSpace)) :
    Module.finrank ℝ
      ((LinearMap.range D.beta) ⧸ LinearMap.ker D.Lambda) = 1 :=
  characteristicCurrent_quotient_finrank_one
    D.toCharacteristicCurrentData

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

/-- Strongest algebraic bridge interface currently needed: the Maxwell positivity witness
is derived from an actual nonzero principal field.  The sole genuinely geometric premise left
is response extensionality through the characteristic variation. -/
structure PrincipalFieldBridgeData where
  beta : P →ₗ[ℝ] KSpace
  ell : P →ₗ[ℝ] ℝ
  response_extensional : ∀ p q : P, beta p = beta q → ell p = ell q
  positiveWitness : P
  smear : ℝ
  E : ℝ
  B : ℝ
  volume : ℝ
  smear_pos : 0 < smear
  field_nonzero : E ≠ 0 ∨ B ≠ 0
  volume_pos : 0 < volume
  response_formula :
    ell positiveWitness =
      maxwellPositiveResponseFromField smear E B volume

theorem PrincipalFieldBridgeData.response_positive
    (D : PrincipalFieldBridgeData (P:=P) (KSpace:=KSpace)) :
    0 < D.ell D.positiveWitness := by
  rw [D.response_formula]
  exact maxwellPositiveResponseFromField_pos
    D.smear D.E D.B D.volume
    D.smear_pos D.field_nonzero D.volume_pos

theorem PrincipalFieldBridgeData.kernel_invisible
    (D : PrincipalFieldBridgeData (P:=P) (KSpace:=KSpace)) :
    LinearMap.ker D.beta ≤ LinearMap.ker D.ell :=
  kernel_invisible_of_response_extensional
    D.beta D.ell D.response_extensional

noncomputable def PrincipalFieldBridgeData.Lambda
    (D : PrincipalFieldBridgeData (P:=P) (KSpace:=KSpace)) :
    LinearMap.range D.beta →ₗ[ℝ] ℝ :=
  characteristicCovectorOfKernel D.beta D.ell D.kernel_invisible

theorem principalFieldBridge_factorization
    (D : PrincipalFieldBridgeData (P:=P) (KSpace:=KSpace)) :
    D.Lambda.comp D.beta.rangeRestrict = D.ell :=
  characteristicCovectorOfKernel_factorization
    D.beta D.ell D.kernel_invisible

theorem principalFieldBridge_Lambda_nonzero
    (D : PrincipalFieldBridgeData (P:=P) (KSpace:=KSpace)) :
    D.Lambda ≠ 0 := by
  exact descended_covector_nonzero
    D.beta.rangeRestrict D.Lambda D.ell
    (principalFieldBridge_factorization D)
    (covector_nonzero_of_positive
      D.ell D.positiveWitness D.response_positive)

theorem principalFieldBridge_Lambda_unique
    (D : PrincipalFieldBridgeData (P:=P) (KSpace:=KSpace))
    (Λ' : LinearMap.range D.beta →ₗ[ℝ] ℝ)
    (hΛ' : Λ'.comp D.beta.rangeRestrict = D.ell) :
    Λ' = D.Lambda :=
  characteristicCovectorOfKernel_unique
    D.beta D.ell D.kernel_invisible Λ' hΛ'

theorem principalFieldBridge_quotient_finrank_one
    (D : PrincipalFieldBridgeData (P:=P) (KSpace:=KSpace)) :
    Module.finrank ℝ
      ((LinearMap.range D.beta) ⧸ LinearMap.ker D.Lambda) = 1 :=
  clockQuotient_finrank_one
    D.Lambda (principalFieldBridge_Lambda_nonzero D)

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
#check syngeImplicitEndpoint
#check syngeImplicitEndpoint_eventually_eq_iff
#check syngeImplicitEndpoint_eventually_solves
#check syngeImplicitEndpoint_hasStrictFDerivAt
#check syngeImplicitEndpoint_continuousAt
#check syngeImplicitEndpoint_tendsto
#check kerrChristoffelPartial_lower_symmetric
#check kerrConnectionProductTrace_symmetric
#check kerrRicciCovFromMetric_contracted
#check kerrRicci_tphi_symmetric
#check kerrChristoffelTrace_theta_hasDerivAt_r
#check kerrChristoffelTracePartial_r_theta
#check kerrRicci_thetar_reduction
#check kerrRicci_thetar_zero
#check kerrRicci_thetar_eq_target
#check kerrChristoffel_r_rtheta_hasDerivAt_r
#check kerrChristoffel_theta_rtheta_hasDerivAt_theta
#check kerrChristoffelTrace_r_hasDerivAt_theta
#check kerrChristoffelPartial_r_rtheta
#check kerrChristoffelPartial_theta_rtheta
#check kerrChristoffelTracePartial_theta_r
#check kerrRicci_rtheta_reduction
#check kerrRicci_rtheta_zero
#check kerrRicci_rtheta_eq_target
#check kerrChristoffelTrace
#check kerrConnectionCrossTrace
#check kerrChristoffel_r_rtheta
#check kerrChristoffel_theta_rtheta
#check kerrChristoffelTrace_r
#check kerrChristoffelTrace_theta
#check kerrConnectionCrossTrace_formula
#check kerrRicci_stationary_meridional_zero
#check kerrRicci_stationary_meridional_eq_target
#check kerrEinsteinTargetRicciCoordinate_stationary_parity
#check kerrEinsteinTargetRicciCoordinate_zero_of_odd_stationary
#check kerrRicciCovFromMetric_eq_target_of_odd_stationary
#check kerrChristoffelPartial_zero_of_odd_stationary
#check kerrRicciCovFromMetric_stationary_parity
#check kerrRicciCovFromMetric_zero_of_odd_stationary
#check kerrStationarySign
#check kerrChristoffel_stationary_parity
#check kerrChristoffel_zero_of_odd_stationary
#check kerrEinsteinTargetRicciCoordinate
#check kerrEinsteinTargetRicciCov_eq_coordinate
#check kerrMetricDerivativeRegular
#check kerrMetricPartial_eq_regular
#check kerrChristoffelRegular
#check kerrChristoffel_eq_regular
#check kerrMetricRadialDerivative
#check kerrMetricPolarDerivative
#check kerrMetricPartial_r
#check kerrMetricPartial_theta
#check kerrMetricPartial_t
#check kerrMetricPartial_phi
#check kerrGtt_alt
#check kerrGtPhi_alt
#check kerrGPhiPhi_alt
#check kerrH_hasDerivAt_r
#check kerrGtt_hasDerivAt_r
#check kerrGtt_hasDerivAt_theta
#check kerrGtPhi_hasDerivAt_r
#check kerrGtPhi_hasDerivAt_theta
#check kerrGrr_hasDerivAt_r
#check kerrGrr_hasDerivAt_theta
#check kerrGthetaTheta_hasDerivAt_r
#check kerrGthetaTheta_hasDerivAt_theta
#check kerrGPhiPhi_hasDerivAt_r
#check kerrGPhiPhi_hasDerivAt_theta
#check kerrCoordPartial
#check kerrMetricPartial
#check kerrMetricPartial_symmetric
#check kerrChristoffel
#check kerrChristoffel_lower_symmetric
#check kerrChristoffelPartial
#check kerrRicciCovFromMetric
#check kerrScalarCurvatureFromMetric
#check kerrEinsteinCovFromMetric
#check kerrPrincipalEnergyDensity_formula
#check kerrRicciFrameMixedCoeff_eq_EinsteinMaxwell
#check kerrEinsteinTarget_frame_equation
#check kerrEinsteinTargetRicciTrace_eq_frame_sum
#check kerrEinsteinTargetRicci_trace_zero
#check kerrEvenRicciObligations
#check kerrFullRicciEquation_iff_even_obligations
#check kerrEinsteinEquation_from_evenRicciObligations
#check kerrSixRicciObligations
#check kerrEvenRicciObligations_iff_six
#check kerrFullRicciEquation_iff_six_obligations
#check kerrEinsteinEquation_from_sixRicciObligations
#check kerrEinsteinTargetRicciCoordinate_symmetric
#check kerrFiveRicciObligations
#check kerrFourRicciObligations
#check kerrFiveRicciObligations_iff_four
#check kerrFullRicciEquation_iff_four_obligations
#check kerrSixRicciObligations_iff_five
#check kerrFullRicciEquation_iff_five_obligations
#check kerrEinsteinEquation_from_fiveRicciObligations
#check kerrEinsteinTargetRicci_frame_norm
#check kerrEinsteinTargetRicci_frame_norm_formula
#check kerrCoframe0_norm
#check kerrCoframe1_norm
#check kerrCoframe2_norm
#check kerrCoframe3_norm
#check kerrCoframe0_orthogonal_3
#check kerrCoframe_nonstationary_orthogonality
#check kerrCoframe_orthonormal
#check relativeAction_defect_ratio
#check action_carrier_optical_ratio_identity
#check relativeActionValue_exchange
#check relativeActionValue_deriv_zero
#check relativeActionValue_diagonal
#check relativeActionDefect_hasDerivAt_zero
#check relativeAction_fixed_point_jet
#check einsteinMaxwellLagrangianDensity_decomposition
#check einsteinMaxwellLagrangianDensity_hasDerivAt_line_zero
#check einsteinMaxwellLagrangianDensity_line_deriv_zero
#check reciprocalLagrangian
#check reciprocalLagrangian_exchange
#check reciprocalLagrangianNormalJet
#check linearDescendant_reciprocal
#check linearDescendant_normalJet
#check linearDescendant_normalJet_of_opposite
#check linearDescendant_reciprocal_hasDerivAt_zero
#check scaledEinsteinMaxwellSectorValue_factorization
#check relativeActionValue_eq_reciprocalLagrangian
#check relativeActionDefect_eq_reciprocalLagrangian
#check relativeSymplecticMinus_apply
#check relativeSymplecticMinus_apply_eq_half_derivative
#check relativeLiouvilleCovector_apply
#check relativeSymplecticMinus_skew
#check relativeLiouvilleCovector_horizontal
#check kerrNewman_forced_specialization_certificate
#check principalField_forced_core_chain
#check kerr_metric_det_eq_scalar
#check kerrVolumeDensity_sq
#check kerrVolumeDensity_eq_sqrt_neg_det
#check kerrMetricCov_symmetric
#check kerrMetricInv_symmetric
#check kerrMetric_inverse_certificate
#check principalFieldEnergyDensity_pos_of_nonzero
#check principalStressFromF_00
#check principalScaledResidualFromF_zero
#check principalScaledResidualFromF_hasDerivAt_zero
#check principalScaledResidualFromF_deriv_zero
#check principalField_solution_preserving_iff
#check principalScaledResidualFromF_00_zero_iff
#check principalTO_physicalU
#check principalTOLinear_physicalU
#check principalPhysicalU_background_unit
#check principal_clock_proper_time_bridge
#check kerrMaxwell_bianchi_t
#check kerrMaxwell_bianchi_phi
#check kerrMaxwell_equations_scalar_certificate
#check kerrRaisedField_components
#check kerrDensitizedField_from_metric
#check kerrMaxwell_source_free_certificate
#check kerr_stationary_block_det
#check kerr_metric_det
#check kerr_stationary_inverse_block
#check kerrPrincipalE_hasDerivAt_r
#check kerrPrincipalE_hasDerivAt_theta
#check kerrPrincipalB_hasDerivAt_r
#check kerrPrincipalB_hasDerivAt_theta
#check kerrMaxwell_divergence_t
#check kerrMaxwell_divergence_phi
#check principalRicciFromF_eq_Einstein
#check principalRicciFromEinstein_trace_zero
#check principalEinsteinTensorFromF_eq_stress
#check principalJetFromF_eq_minus_two_EinsteinRicci
#check relativeConstraintVariation_eq_residual_deriv
#check iyerWald_boundary_compensation_linear
#check iyerWald_bulk_response_linear
#check iyerWald_compensated_eq_carrierBulkResponse
#check iyerWald_half_compensated_eq_stressResponse
#check PrincipalCarrierCharacteristicInput.globalLocalClockEquiv
#check principalCarrierCharacteristic_globalLocal_pullback
#check principalCarrierCharacteristic_globalUnit_maps_local
#check principalCarrierCharacteristic_normalizationBridge
#check principalCarrierCharacteristic_clock_chain
#check PrincipalLagrangianCharacteristicInput
#check PrincipalLagrangianCharacteristicInput.relativeNormalJet
#check PrincipalLagrangianCharacteristicInput.iwCharacteristicCurrent
#check principalLagrangianCharacteristic_iwCurrent_eq_stress
#check principalLagrangianCharacteristic_iwCurrent_eq_characteristicCurrent
#check principalLagrangianCharacteristic_iwCurrent_nonzero
#check principalLagrangianCharacteristic_clock_chain
#check SyngeEndpointJetData.linearizedPlus
#check SyngeEndpointJetData.dThetaPlus_unique
#check SyngeEndpointJetData.dThetaMinus_unique
#check endpointCovector_decomposition_unique
#check SyngeEndpointJetData.clock_radial_unique
#check SyngeEndpointJetData.firstJet_forced_unique
#check SyngeEndpointJetData.linearizedMinus
#check SyngeEndpointJetData.sigmaXPlus_null
#check SyngeEndpointJetData.endpoint_eikonals_null
#check SyngeEndpointJetData.toNullEndpointPairData
#check SyngeEndpointJetData.optical_closure
#check principalStressLinearFromF_apply
#check principalStressLinearFromF_time_eigen
#check principalStressResponse_formula
#check principalFieldEnergyDensity_pos
#check principalStressResponse_pos
#check PrincipalCarrierCharacteristicInput.response_positive
#check PrincipalCarrierCharacteristicInput.toCharacteristicCurrentData
#check principalCarrierCharacteristic_current
#check principalCarrierCharacteristic_Lambda_nonzero
#check principalCarrierCharacteristic_quotient_finrank_one
#check principalCarrierCharacteristic_clock_nonzero
#check principalNullPair_normalized
#check principalUhat_from_null_pair
#check principalEhat_from_null_pair
#check principalBoostedNullPair_normalized
#check normalized_null_rescaling_is_boost
#check principalJetFromF_trace_sq
#check principalJetFromF_chi_from_trace
#check principalRicciFromF_trace_sq
#check principalField_chiS_invariants
#check normalizedCarrierEndomorphism_scale_invariant
#check normalizedCarrierEndomorphism_common_scale
#check involution_projectors_scale_invariant
#check carrierMagnitude_common_scale
#check carrier_chi_common_scale
#check common_scale_invariance_implies_homogeneous
#check common_scale_invariance_forces_linear_factor
#check conformal_factor_forced_from_common_scale
#check opticalMetric2_inverse
#check opticalInverseMetric2_basis_norms
#check opticalMetric2_lapse_form
#check opticalInverseMetric2_lapse_form
#check endpointCovector_reconstruction
#check NullEndpointPairData.endpoint_eikonals_null
#check NullEndpointPairData.reconstruction
#check NullEndpointPairData.optical_closure
#check NullEndpointPairData.equal_norm_forced
#check PrincipalFieldCurrentData.current_positive
#check PrincipalFieldCurrentData.toCharacteristicCurrentData
#check principalFieldCurrent_factorization
#check principalFieldCurrent_Lambda_nonzero
#check principalFieldCurrent_Lambda_unique
#check principalFieldCurrent_quotient_finrank_one
#check characteristicCurrentDataOfCarrier
#check characteristicCurrentDataOfCarrier_current
#check characteristicCurrentDataOfCarrier_ell
#check characteristicCurrentDataOfCarrier_Lambda_apply
#check halfCarrierBulkCurrent_eq_stressResponse
#check half_carrier_bridge_scalar
#check characteristicCurrent_factorization
#check CharacteristicCurrentData.kernel_invisible
#check CharacteristicCurrentData.ell_positive
#check characteristicCurrent_Lambda_nonzero
#check characteristicCurrent_Lambda_unique
#check characteristicCurrent_quotient_finrank_one
#check characteristicCurrent_clockCovector_nonzero
#check principalFieldEnergyDensity_neg
#check principalChi_neg
#check principalStressFromF_neg
#check principalJetFromF_neg
#check clockLiouville_horizontal_Euler
#check clockLiouville_dilation_pullback
#check relativeSymplecticPlus_hasDerivAt_zero
#check relativeSymplecticMinus_eq_half_derivative
#check relativeSymplecticMinus_exchange
#check synchronizationCovector_decomposition
#check synchronizationCovector_unique
#check synchronizationCovector_vanishes_on_clock
#check principalSynchronization_vanishes
#check carrierJetCurrent_eq_stressBridgeCurrent
#check carrierBulkResponse_eq_minus_two_stressResponse
#check carrier_bridge_scalar
#check covectorWedge4_smul_smul
#check kerrCoordinateField_components
#check kerrCoordinateField_eq_CarterCoframe
#check kerrPotential_to_CarterPrincipalField
#check carterTemporalCoframe_on_observer
#check carterAxialOneForm_on_observer
#check kerrMaxwell_Carter_principal_structure
#check principalEpsilonHSpatialCoeff_eq
#check principalBridgeSpatialCoeff_formula
#check principalBridgeSpatialCoeff_unit
#check principalBridgeSpatialCoeff_factor
#check principalBridgeSpatialCoeff_unit_ne_zero
#check principalBridgeSpatialCoeff_ratio_forced
#check clockTransport_projected_zero_iff
#check principalFrobenius_all_zero_iff
#check clockDilation_undilate
#check clockLiouville_unique_of_homogeneity
#check clockCoverOneForm_unique
#check principalClockRate_sq
#check principalClockRate_eq_invariant_fourth_root
#check principalClockRate_eq_energy_density
#check principalClockRate_eq_ricci_fourth_root
#check principalClockRate_three_way
#check principalPointResponse_formula
#check principalPointResponse_unit
#check principalPointResponse_factor
#check principalPointResponse_unit_ne_zero
#check principalPointResponse_ratio_forced
#check clockTransportTwoForm_skew
#check clockTransport_spatial
#check clockTransport_mixed
#check clockTransport_mixed_logK
#check principalFrobeniusSpatialComponent_eq
#check principalFrobeniusSpatialComponent_zero_iff
#check endpointClock_hasDerivAt
#check endpointClock_deriv
#check radarClockTime_hasDerivAt
#check radarClockRadius_hasDerivAt
#check radarClockRadius_zero_of_coincident_endpoint
#check radarClockRadius_unit_radial_jet
#check radarClockTime_unit_clock_jet
#check principalLocalQuotientUnit_normalized
#check principalLocalQuotient_finrank_one
#check globalToPrincipalLocalClockMap_apply
#check globalToPrincipalLocalClockMap_pullback
#check globalToPrincipalLocalClockMap_bijective
#check globalToPrincipalLocalClockEquiv
#check globalClockUnit_maps_to_principalUnit
#check normalizationBridge_principal
#check principalTO_ker_eq_spatial
#check principalLocalLift_mk
#check principal_local_remainder_mem_kernel
#check principal_quotient_eq_timelike_rep
#check principalLocalLift_inverts_timelike
#check principalLocalLift_section
#check kerrRadialFieldBlock_carter_aligned
#check kerrPolarFieldBlock_carter_aligned
#check kerrPotential_metric_principal_alignment
#check kerrResolvingQMinus_ne_zero
#check kerrResolving_balance_rapidity_zero
#check kerrResolving_balanced_observer_unboosted
#check kerr_relative_rest_carter_regular
#check carterNumerator_time_leg
#check carterNumerator_axial_leg
#check kerrStationaryNormSq_smul
#check carterNumerator_norm
#check carterObserver_unit_timelike
#check Sigma_hasDerivAt_theta
#check kerrPotentialT_hasDerivAt_r
#check kerrPotentialPhi_hasDerivAt_r
#check kerrPotentialT_hasDerivAt_theta
#check kerrPotentialPhi_hasDerivAt_theta
#check kerrPotential_field_factorization
#check maxwellPositiveResponseFromField_eq
#check maxwellPositiveResponseFromField_pos
#check PrincipalFieldBridgeData.response_positive
#check PrincipalFieldBridgeData.Lambda
#check principalFieldBridge_factorization
#check principalFieldBridge_Lambda_nonzero
#check principalFieldBridge_Lambda_unique
#check principalFieldBridge_quotient_finrank_one
#check presymplecticReductionForm
#check presymplecticReductionForm_mk
#check presymplecticReductionForm_left_nondegenerate
#check presymplecticReductionForm_right_nondegenerate
#check clockAccumulation_hasDerivAt
#check clockAccumulation_deriv
#check clockAccumulation_origin
#check clockAccumulation_deriv_pos
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
#check LagrangianIyerWaldOperators.omegaXY
#check LagrangianIyerWaldOperators.compensated_eq_constraint
#check LagrangianIyerWaldOperators.omegaXY_unique
#check LagrangianIyerWaldOperators.omegaXY_existsUnique
#check LagrangianIyerWaldOperators.constraint_normalJet_of_opposite
#check LagrangianIyerWaldOperators.compensated_relative_normal
#check lagrangianIyerWald_compensated_eq_carrierBulkResponse
#check lagrangianIyerWald_half_compensated_eq_stressResponse
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
#print axioms RelativeRest.relativeAction_fixed_point_jet
#print axioms RelativeRest.einsteinMaxwellLagrangianDensity_decomposition
#print axioms RelativeRest.linearDescendant_reciprocal
#print axioms RelativeRest.linearDescendant_normalJet_of_opposite
#print axioms RelativeRest.linearDescendant_reciprocal_hasDerivAt_zero
#print axioms RelativeRest.relativeSymplecticMinus_from_lagrangian_normalJet
#print axioms RelativeRest.relativeConstraintResidual_deriv_from_lagrangian
#print axioms RelativeRest.conformal_factor_forced_from_common_scale
#print axioms RelativeRest.carrier_chi_common_scale
#print axioms RelativeRest.normalizedCarrierEndomorphism_common_scale
#print axioms RelativeRest.involution_projectors_scale_invariant
#print axioms RelativeRest.relationalObservable_gauge_invariant
#print axioms RelativeRest.relationalObservable_deriv
#print axioms RelativeRest.implicit_endpoint_covector_null
#print axioms RelativeRest.NullEndpointPairData.endpoint_eikonals_null
#print axioms RelativeRest.NullEndpointPairData.optical_closure
#print axioms RelativeRest.SyngeEndpointJetData.dThetaPlus_unique
#print axioms RelativeRest.SyngeEndpointJetData.dThetaMinus_unique
#print axioms RelativeRest.SyngeEndpointJetData.firstJet_forced_unique
#print axioms RelativeRest.SyngeEndpointJetData.endpoint_eikonals_null
#print axioms RelativeRest.SyngeEndpointJetData.optical_closure
#print axioms RelativeRest.syngeImplicitEndpoint_eventually_solves
#print axioms RelativeRest.syngeImplicitEndpoint_hasStrictFDerivAt
#print axioms RelativeRest.opticalMetric2_inverse
#print axioms RelativeRest.opticalMetric2_lapse_form
#print axioms RelativeRest.clockAccumulation_hasDerivAt
#print axioms RelativeRest.clockTransport_spatial
#print axioms RelativeRest.clockTransport_mixed_logK
#print axioms RelativeRest.principalFrobeniusSpatialComponent_zero_iff
#print axioms RelativeRest.clockTransport_projected_zero_iff
#print axioms RelativeRest.principalFrobenius_all_zero_iff
#print axioms RelativeRest.principalSynchronization_vanishes
#print axioms RelativeRest.radarClockRadius_unit_radial_jet
#print axioms RelativeRest.radarClockTime_unit_clock_jet
#print axioms RelativeRest.primitive_relative_weights_reciprocal_iff_four
#print axioms RelativeRest.scalar_backbone_from_einstein_maxwell
#print axioms RelativeRest.rescaled_solution_preserving_iff
#print axioms RelativeRest.characteristic_half_contraction_from_relative_scaling
#print axioms RelativeRest.LagrangianIyerWaldOperators.compensated_eq_constraint
#print axioms RelativeRest.LagrangianIyerWaldOperators.omegaXY_existsUnique
#print axioms RelativeRest.LagrangianIyerWaldOperators.compensated_relative_normal
#print axioms RelativeRest.lagrangianIyerWald_compensated_eq_carrierBulkResponse
#print axioms RelativeRest.lagrangianIyerWald_half_compensated_eq_stressResponse
#print axioms RelativeRest.iyerWald_compensated_eq_carrierBulkResponse
#print axioms RelativeRest.iyerWald_half_compensated_eq_stressResponse
#print axioms RelativeRest.relativeSymplecticMinus_eq_half_derivative
#print axioms RelativeRest.relativeLiouvilleCovector_horizontal
#print axioms RelativeRest.carrierJetCurrent_eq_stressBridgeCurrent
#print axioms RelativeRest.carrierBulkResponse_eq_minus_two_stressResponse
#print axioms RelativeRest.halfCarrierBulkCurrent_eq_stressResponse
#print axioms RelativeRest.principalLocalClockRatio_forced
#print axioms RelativeRest.principal_clock_proper_time_bridge
#print axioms RelativeRest.principalPointResponse_ratio_forced
#print axioms RelativeRest.principalBridgeSpatialCoeff_ratio_forced
#print axioms RelativeRest.principalClockRate_three_way
#print axioms RelativeRest.principalLocalLift_section
#print axioms RelativeRest.globalToPrincipalLocalClockMap_pullback
#print axioms RelativeRest.normalizationBridge_principal
#print axioms RelativeRest.principalMaxwell_timelike_eigen_from_chi
#print axioms RelativeRest.principalStressFromF_eq_principalStress
#print axioms RelativeRest.principalScaledResidualFromF_deriv_zero
#print axioms RelativeRest.principalScaledResidualFromF_00_zero_iff
#print axioms RelativeRest.principalJetFromF_rainich
#print axioms RelativeRest.principalEinsteinTensorFromF_eq_stress
#print axioms RelativeRest.principalJetFromF_eq_minus_two_EinsteinRicci
#print axioms RelativeRest.principalField_chiS_invariants
#print axioms RelativeRest.principalNullPair_normalized
#print axioms RelativeRest.normalized_null_rescaling_is_boost
#print axioms RelativeRest.principalJetFromF_neg
#print axioms RelativeRest.principalNormalizedJetFromFApply_eq_involution
#print axioms RelativeRest.principalMaxwell_form_invariant_magnitude
#print axioms RelativeRest.defect_from_on_shell_equation
#print axioms RelativeRest.scaledResidual_first_jet_eq_minus_two_ricci_from_EM
#print axioms RelativeRest.boost_balance_exists_unique_of_nonnull
#print axioms RelativeRest.rapidity_forced_by_normalized_boost
#print axioms RelativeRest.extensionalBridge_Lambda_unique
#print axioms RelativeRest.maxwellBridge_Lambda_unique
#print axioms RelativeRest.principalFieldBridge_Lambda_unique
#print axioms RelativeRest.characteristicCurrent_Lambda_unique
#print axioms RelativeRest.characteristicCurrent_quotient_finrank_one
#print axioms RelativeRest.characteristicCurrentDataOfCarrier_Lambda_apply
#print axioms RelativeRest.principalStressResponse_pos
#print axioms RelativeRest.principalCarrierCharacteristic_quotient_finrank_one
#print axioms RelativeRest.principalCarrierCharacteristic_clock_chain
#print axioms RelativeRest.principalLagrangianCharacteristic_iwCurrent_eq_characteristicCurrent
#print axioms RelativeRest.principalLagrangianCharacteristic_iwCurrent_nonzero
#print axioms RelativeRest.principalLagrangianCharacteristic_clock_chain
#print axioms RelativeRest.principalField_forced_core_chain
#print axioms RelativeRest.principalFieldCurrent_Lambda_unique
#print axioms RelativeRest.principalFieldCurrent_quotient_finrank_one
#print axioms RelativeRest.reeb_direction_unique
#print axioms RelativeRest.clock_section_reeb_existsUnique
#print axioms RelativeRest.clockLiouville_unique_of_homogeneity
#print axioms RelativeRest.clockLiouville_dilation_pullback
#print axioms RelativeRest.clockQuotientDualEquiv
#print axioms RelativeRest.quotientBilinearForm_unique
#print axioms RelativeRest.presymplecticReductionForm_left_nondegenerate
#print axioms RelativeRest.causal_extended_endpoints_mono
#print axioms RelativeRest.kerrLogChi_hasDerivAt_r
#print axioms RelativeRest.kerrNewman_mino_clock_forced
#print axioms RelativeRest.kerrNewman_mino_clock_from_principal_EM
#print axioms RelativeRest.kerrMinoClockFromPrincipalEM
#print axioms RelativeRest.kerrPotential_field_factorization
#print axioms RelativeRest.kerr_stationary_inverse_block
#print axioms RelativeRest.kerrMetric_inverse_certificate
#print axioms RelativeRest.kerrGtt_hasDerivAt_r
#print axioms RelativeRest.kerrGtPhi_hasDerivAt_theta
#print axioms RelativeRest.kerrGrr_hasDerivAt_r
#print axioms RelativeRest.kerrGPhiPhi_hasDerivAt_theta
#print axioms RelativeRest.kerrMetricPartial_symmetric
#print axioms RelativeRest.kerrMetricPartial_r
#print axioms RelativeRest.kerrMetricPartial_theta
#print axioms RelativeRest.kerrMetricPartial_eq_regular
#print axioms RelativeRest.kerrChristoffel_eq_regular
#print axioms RelativeRest.kerrChristoffel_lower_symmetric
#print axioms RelativeRest.kerrChristoffel_stationary_parity
#print axioms RelativeRest.kerrChristoffel_zero_of_odd_stationary
#print axioms RelativeRest.kerrChristoffel_r_rtheta
#print axioms RelativeRest.kerrChristoffel_theta_rtheta
#print axioms RelativeRest.kerrChristoffelTrace_r
#print axioms RelativeRest.kerrChristoffelTrace_theta
#print axioms RelativeRest.kerrConnectionCrossTrace_formula
#print axioms RelativeRest.kerrChristoffelPartial_zero_of_odd_stationary
#print axioms RelativeRest.kerrRicciCovFromMetric_stationary_parity
#print axioms RelativeRest.kerrRicciCovFromMetric_zero_of_odd_stationary
#print axioms RelativeRest.kerrEinsteinTargetRicciCoordinate_stationary_parity
#print axioms RelativeRest.kerrRicciCovFromMetric_eq_target_of_odd_stationary
#print axioms RelativeRest.kerrRicci_stationary_meridional_zero
#print axioms RelativeRest.kerrRicci_stationary_meridional_eq_target
#print axioms RelativeRest.kerrChristoffel_r_rtheta_hasDerivAt_r
#print axioms RelativeRest.kerrChristoffelTrace_r_hasDerivAt_theta
#print axioms RelativeRest.kerrRicci_rtheta_zero
#print axioms RelativeRest.kerrRicci_rtheta_eq_target
#print axioms RelativeRest.kerrChristoffelPartial_lower_symmetric
#print axioms RelativeRest.kerrConnectionProductTrace_symmetric
#print axioms RelativeRest.kerrRicci_tphi_symmetric
#print axioms RelativeRest.kerrChristoffelTrace_theta_hasDerivAt_r
#print axioms RelativeRest.kerrRicci_thetar_zero
#print axioms RelativeRest.kerrRicci_thetar_eq_target
#print axioms RelativeRest.kerrCoframe_orthonormal
#print axioms RelativeRest.kerrEinsteinTargetRicci_trace_zero
#print axioms RelativeRest.kerrFullRicciEquation_iff_even_obligations
#print axioms RelativeRest.kerrEinsteinEquation_from_evenRicciObligations
#print axioms RelativeRest.kerrFullRicciEquation_iff_six_obligations
#print axioms RelativeRest.kerrEinsteinEquation_from_sixRicciObligations
#print axioms RelativeRest.kerrFullRicciEquation_iff_five_obligations
#print axioms RelativeRest.kerrEinsteinEquation_from_fiveRicciObligations
#print axioms RelativeRest.kerrEinsteinTargetRicciCov_eq_coordinate
#print axioms RelativeRest.kerrEinsteinTargetRicci_frame_norm_formula
#print axioms RelativeRest.kerrEinsteinTarget_frame_equation
#print axioms RelativeRest.kerrVolumeDensity_eq_sqrt_neg_det
#print axioms RelativeRest.kerr_metric_det
#print axioms RelativeRest.kerrMaxwell_divergence_t
#print axioms RelativeRest.kerrMaxwell_divergence_phi
#print axioms RelativeRest.kerrMaxwell_source_free_certificate
#print axioms RelativeRest.kerrMaxwell_equations_scalar_certificate
#print axioms RelativeRest.kerrCoordinateField_eq_CarterCoframe
#print axioms RelativeRest.kerrPotential_to_CarterPrincipalField
#print axioms RelativeRest.kerrPotential_metric_principal_alignment
#print axioms RelativeRest.kerr_relative_rest_carter_certificate
#print axioms RelativeRest.carterObserver_unit_timelike
#print axioms RelativeRest.kerrMaxwell_Carter_principal_structure
#print axioms RelativeRest.kerr_relative_rest_carter_regular
#print axioms RelativeRest.kerrNewman_forced_specialization_certificate
#print axioms RelativeRest.kerr_regular_first_or_second_radial_jet_resolves
