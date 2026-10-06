import RelativeRest_DeepPass30

/-!
# Relative Rest: deep forced pass 31

Derive chi=sqrt(K) from the fixed-point tensor identity J=-2R.

Let C be the bilinear contraction induced by the inverse metric at a point.  Bilinearity alone gives
  C(J,J)=4 C(R,R)
when J=-2R.  Therefore, with
  K=C(R,R),
  chi=(1/2) sqrt(C(J,J)),
and K>=0, the carrier magnitude is forced to be chi=sqrt(K).

This removes chi=sqrt(K) as an independent scalar hypothesis in the chronometric chain.
-/

noncomputable section

open Function Set

namespace RelativeRest

section CarrierCurvatureMagnitude

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (C : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

theorem bilinearContraction_smul
    (x y : V)
    (a b : ℝ) :
    C (a • x) (b • y) =
      (a * b) * C x y := by
  simp [map_smul]
  ring

/-- J=-2R forces the quadratic contraction J.J=4 R.R. -/
theorem jet_contraction_eq_four_curvature
    (J R : V)
    (hJ : J = (-2 : ℝ) • R) :
    C J J = 4 * C R R := by
  rw [hJ, bilinearContraction_smul]
  ring

/-- The Rainich carrier magnitude is exactly sqrt(K) once J=-2R. -/
theorem carrierMagnitude_eq_sqrt_curvature
    (J R : V)
    (K chi : ℝ)
    (hJ : J = (-2 : ℝ) • R)
    (hK : K = C R R)
    (hKnonneg : 0 ≤ K)
    (hchi : chi = (1 / 2 : ℝ) * Real.sqrt (C J J)) :
    chi = Real.sqrt K := by
  have hJJ :
      C J J = 4 * K := by
    rw [jet_contraction_eq_four_curvature C J R hJ, ← hK]
  have hJJnonneg : 0 ≤ C J J := by
    rw [hJJ]
    positivity
  have hsqrtJJ :
      (Real.sqrt (C J J))^2 = C J J :=
    Real.sq_sqrt hJJnonneg
  have hchi_nonneg : 0 ≤ chi := by
    rw [hchi]
    positivity
  have hchi_sq : chi^2 = K := by
    rw [hchi]
    nlinarith [hsqrtJJ, hJJ]
  have hsqrtK_sq :
      (Real.sqrt K)^2 = K :=
    Real.sq_sqrt hKnonneg
  have hsqrtK_nonneg : 0 ≤ Real.sqrt K :=
    Real.sqrt_nonneg K
  nlinarith

/-- The positive clock rate is literally the iterated square root sqrt(sqrt K),
i.e. the positive real fourth root K^(1/4). -/
theorem curvature_forces_clock_rate
    (J R : V)
    (K chi omega : ℝ)
    (hJ : J = (-2 : ℝ) • R)
    (hK : K = C R R)
    (hKnonneg : 0 ≤ K)
    (hchi : chi = (1 / 2 : ℝ) * Real.sqrt (C J J))
    (homega : omega = Real.sqrt chi) :
    omega = Real.sqrt (Real.sqrt K) := by
  rw [homega,
    carrierMagnitude_eq_sqrt_curvature
      C J R K chi hJ hK hKnonneg hchi]

/-- Consequently omega=sqrt(chi) is the positive fourth-root rate of K without a separately
supplied chi=sqrt(K) hypothesis. -/
theorem curvature_forces_clock_fourth_power
    (J R : V)
    (K chi omega : ℝ)
    (hJ : J = (-2 : ℝ) • R)
    (hK : K = C R R)
    (hKnonneg : 0 ≤ K)
    (hchi : chi = (1 / 2 : ℝ) * Real.sqrt (C J J))
    (homega : omega = Real.sqrt chi) :
    omega^4 = K := by
  have hchisqrt :=
    carrierMagnitude_eq_sqrt_curvature
      C J R K chi hJ hK hKnonneg hchi
  have hchi_nonneg : 0 ≤ chi := by
    rw [hchisqrt]
    positivity
  have homega_sq : omega^2 = chi := by
    rw [homega]
    exact Real.sq_sqrt hchi_nonneg
  rw [show omega^4 = (omega^2)^2 by ring,
      homega_sq, hchisqrt]
  exact Real.sq_sqrt hKnonneg

end CarrierCurvatureMagnitude

end RelativeRest
