import RelativeRest_Maxwell_Action

/-!
# Field-strength-level Maxwell stress and homothetic covariance

This file closes a specific upstream gap in the manuscript's action/field chain.
It defines the covariant Maxwell stress from a field two-form and a diagonal
inverse metric, and proves its exact scaling under a constant four-dimensional
metric homothety and potential rescaling.

The result is valid for arbitrary field components, without choosing an E/B
principal frame or postulating the stress rescaling. The Einstein-tensor
invariance under a constant homothety is a separate differential-geometric
obligation, NOT proved here.

The second section proves an important *logical scope condition*: without
the destruction of residual Lorentz boost isotropy, no nonzero vector can be
selected intrinsically as a fixed point of all the surviving boost symmetries.
This identifies a necessary rigidity condition rather than hiding it.
-/

noncomputable section

open scoped BigOperators

namespace RelativeRest
namespace MaxwellAction

abbrev Tensor44 := Fin 4 → Fin 4 → ℝ
abbrev DiagonalInverseMetric := Fin 4 → ℝ

/-- The field-linear term F_a^c F_bc in a diagonal inverse metric. -/
def maxwellQuadratic
    (w : DiagonalInverseMetric) (F : Tensor44)
    (a b : Fin 4) : ℝ :=
  ∑ c : Fin 4, w c * F a c * F b c

/-- The electromagnetic scalar F_cd F^cd, with both inverse metrics explicit. -/
def maxwellContraction
    (w : DiagonalInverseMetric) (F : Tensor44) : ℝ :=
  ∑ c : Fin 4, ∑ d : Fin 4,
    w c * w d * F c d * F c d

/-- Covariant Maxwell stress, with the overall conventional 1/(4*pi) suppressed.
    g is the covariant metric; w contains diagonal contravariant metric entries. -/
def maxwellStress
    (g : Tensor44) (w : DiagonalInverseMetric)
    (F : Tensor44) (a b : Fin 4) : ℝ :=
  maxwellQuadratic w F a b -
    (1 / 4 : ℝ) * g a b * maxwellContraction w F

/-- The Maxwell quadratic term carries one inverse metric and two F factors. -/
theorem maxwellQuadratic_scale
    (w : DiagonalInverseMetric) (F : Tensor44)
    (q lam : ℝ) (a b : Fin 4) :
    maxwellQuadratic (fun c => q * w c)
        (fun i j => lam * F i j) a b =
      (q * lam^2) * maxwellQuadratic w F a b := by
  unfold maxwellQuadratic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

/-- F_cd F^cd carries two inverse metrics and two F factors. -/
theorem maxwellContraction_scale
    (w : DiagonalInverseMetric) (F : Tensor44)
    (q lam : ℝ) :
    maxwellContraction (fun c => q * w c)
        (fun i j => lam * F i j) =
      (q^2 * lam^2) * maxwellContraction w F := by
  unfold maxwellContraction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- For mutually inverse constant metric scales h*q=1, the full covariant
    Maxwell tensor scales by the single forced character q*lam^2. -/
theorem maxwellStress_scale
    (g : Tensor44) (w : DiagonalInverseMetric)
    (F : Tensor44) (h q lam : ℝ)
    (hunit : h * q = 1) (a b : Fin 4) :
    maxwellStress
        (fun i j => h * g i j)
        (fun c => q * w c)
        (fun i j => lam * F i j) a b =
      (q * lam^2) * maxwellStress g w F a b := by
  have hq : h * q^2 = q := by
    calc
      h * q^2 = (h * q) * q := by ring
      _ = q := by rw [hunit]; ring
  unfold maxwellStress
  rw [maxwellQuadratic_scale, maxwellContraction_scale]
  calc
    (q * lam^2) * maxwellQuadratic w F a b -
        (1 / 4 : ℝ) * (h * g a b) *
          ((q^2 * lam^2) * maxwellContraction w F) =
      (q * lam^2) * maxwellQuadratic w F a b -
        (1 / 4 : ℝ) * ((h * q^2) * lam^2) *
          (g a b * maxwellContraction w F) := by ring
    _ = (q * lam^2) *
        (maxwellQuadratic w F a b -
          (1 / 4 : ℝ) * g a b * maxwellContraction w F) := by
      rw [hq]
      ring

/-- The fixed Minkowski orthonormal-frame metric. -/
def etaCovariant : Tensor44 :=
  fun a b => if a = b then lorentzSign a else 0

/-- Canonically normalized local covariant Maxwell tensor without the
    conventional factor 1/(4*pi). -/
def flatMaxwellStress (F : Tensor44) : Tensor44 :=
  maxwellStress etaCovariant lorentzSign F

/-- Gaussian-unit physical Maxwell stress tensor, with the 1/(4*pi)
    restored; the preceding algebra used the unnormalized tensor. -/
def physicalMaxwellStress (F : Tensor44) : Tensor44 :=
  fun a b => (1 / (4 * Real.pi)) * flatMaxwellStress F a b

/-- The physically scaled metric and two-form in an orthonormal chart:
    g -> rho^2 g, F -> lam F, with inverse-metric weight (rho^2)^{-1}. -/
def homotheticMaxwellStress
    (rho lam : ℝ) (F : Tensor44) : Tensor44 :=
  maxwellStress
    (fun a b => rho^2 * etaCovariant a b)
    (fun c => (rho^2)⁻¹ * lorentzSign c)
    (fun a b => lam * F a b)

/-- Direct component-level derivation of the four-dimensional Maxwell stress
    character: T_ab[rho^2 g,lam F] = (lam^2/rho^2) T_ab[g,F].
    No transformation law for T_ab is separately assumed. -/
theorem homotheticMaxwellStress_eq
    (rho lam : ℝ) (hrho : rho ≠ 0) (F : Tensor44)
    (a b : Fin 4) :
    homotheticMaxwellStress rho lam F a b =
      (lam^2 / rho^2) * flatMaxwellStress F a b := by
  have h2 : rho^2 ≠ 0 := pow_ne_zero 2 hrho
  have hunit : rho^2 * (rho^2)⁻¹ = 1 :=
    mul_inv_cancel₀ h2
  unfold homotheticMaxwellStress flatMaxwellStress
  rw [maxwellStress_scale etaCovariant lorentzSign F
    (rho^2) ((rho^2)⁻¹) lam hunit a b]
  rw [div_eq_mul_inv]
  ring

/-- Gauge invariance of the covariant Maxwell tensor now follows from its
    explicitly derived dependence on the antisymmetric field strength. -/
theorem flatMaxwellStress_gauge_invariant
    (D H : PotentialJet)
    (hH : ∀ a b : Fin 4, H a b = H b a) :
    flatMaxwellStress
        (fieldStrength (fun a b => D a b + H a b)) =
      flatMaxwellStress (fieldStrength D) := by
  rw [fieldStrength_gauge_invariant D H hH]

/-- If the Maxwell tensor is nonzero in at least one component, preservation
    under the two independent action-sector scales forces their relative
    stress character to equal one. This is a genuinely non-vacuum condition. -/
theorem relative_scale_forced_of_nonzero_stress
    (rho lam : ℝ) (hrho : rho ≠ 0)
    (F : Tensor44) (a b : Fin 4)
    (hT : flatMaxwellStress F a b ≠ 0)
    (hpreserve : homotheticMaxwellStress rho lam F a b =
        flatMaxwellStress F a b) :
    lam^2 / rho^2 = 1 := by
  rw [homotheticMaxwellStress_eq rho lam hrho F a b] at hpreserve
  have hzero :
      ((lam^2 / rho^2) - 1) * flatMaxwellStress F a b = 0 := by
    nlinarith [hpreserve]
  rcases mul_eq_zero.mp hzero with hratio | hbad
  · exact sub_eq_zero.mp hratio
  · exact False.elim (hT hbad)

/-- The unique-positive-scale version of the previous fixed-point theorem. -/
theorem positive_scales_coincide
    (rho lam : ℝ) (hrho : 0 < rho) (hlam : 0 < lam)
    (F : Tensor44) (a b : Fin 4)
    (hT : flatMaxwellStress F a b ≠ 0)
    (hpreserve : homotheticMaxwellStress rho lam F a b =
        flatMaxwellStress F a b) :
    lam = rho := by
  have hratio :=
    relative_scale_forced_of_nonzero_stress
      rho lam (ne_of_gt hrho) F a b hT hpreserve
  have hrho2 : rho^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hrho)
  have hsq : lam^2 = rho^2 := by
    apply (div_eq_iff hrho2).mp at hratio
    nlinarith [hratio]
  nlinarith

end MaxwellAction

namespace IntrinsicBoostScope

/-- A residual null-frame boost with independent nontrivial real weights. -/
def weightedNullBoost (p q : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (p * v.1, q * v.2)

/-- If neither boost eigenvalue is one, the unique invariant vector is zero.
    Consequently, an invariant unit timelike vector cannot be constructed
    from geometric data retaining such a boost symmetry. -/
theorem nontrivial_null_boost_has_only_zero_fixed_vector
    (p q : ℝ) (hp : p ≠ 1) (hq : q ≠ 1)
    (v : ℝ × ℝ) (hfixed : weightedNullBoost p q v = v) :
    v = (0, 0) := by
  have hfst := congrArg Prod.fst hfixed
  have hsnd := congrArg Prod.snd hfixed
  change p * v.1 = v.1 at hfst
  change q * v.2 = v.2 at hsnd
  have h1 : (p - 1) * v.1 = 0 := by nlinarith [hfst]
  have h2 : (q - 1) * v.2 = 0 := by nlinarith [hsnd]
  have hv1 : v.1 = 0 := by
    rcases mul_eq_zero.mp h1 with hh | hh
    · exact False.elim (hp (sub_eq_zero.mp hh))
    · exact hh
  have hv2 : v.2 = 0 := by
    rcases mul_eq_zero.mp h2 with hh | hh
    · exact False.elim (hq (sub_eq_zero.mp hh))
    · exact hh
  exact Prod.ext hv1 hv2

/-- Actual Lorentz boosts have exp(s), exp(-s) as the null eigenvalues. -/
def lorentzNullBoost (s : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  weightedNullBoost (Real.exp s) (Real.exp (-s)) v

/-- At any nonzero rapidity, no nonzero vector is invariant under a boost. -/
theorem no_nonzero_vector_fixed_by_nonzero_lorentz_boost
    (s : ℝ) (hs : s ≠ 0)
    (v : ℝ × ℝ) (hv : v ≠ (0, 0)) :
    lorentzNullBoost s v ≠ v := by
  have hp : Real.exp s ≠ 1 := by
    intro h
    exact hs (Real.exp_eq_one_iff.mp h)
  have hq : Real.exp (-s) ≠ 1 := by
    intro h
    have hz : -s = 0 := Real.exp_eq_one_iff.mp h
    exact hs (neg_eq_zero.mp hz)
  intro hfix
  exact hv (nontrivial_null_boost_has_only_zero_fixed_vector
    (Real.exp s) (Real.exp (-s)) hp hq v hfix)

end IntrinsicBoostScope
end RelativeRest
