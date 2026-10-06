import RelativeRest_DeepPass5

/-!
# Relative Rest: deep forced pass 6

This layer packages additional end-matter chains:
* the linearized action response sends the common mode to zero and the relative mode to -2 eta;
* the boost defect has the advertised strictly negative derivative on the regular branch;
* the null Maxwell invariant locus makes the mixed stress square nilpotent;
* Kerr--Newman curvature implies the invariant clock and hence the Mino relation in one chain.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-! ## A. Linearized action response -/

section LinearizedActionResponse

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def linearizedActionResponse (eta : V) : R2 →ₗ[ℝ] V where
  toFun v := (v.1 - v.2) • eta
  map_add' x y := by
    rcases x with ⟨x1,x2⟩
    rcases y with ⟨y1,y2⟩
    simp
    module
  map_smul' c x := by
    rcases x with ⟨x1,x2⟩
    simp
    module

@[simp] theorem linearizedActionResponse_CA
    (eta : V) :
    linearizedActionResponse eta CA = 0 := by
  simp [linearizedActionResponse, CA]

@[simp] theorem linearizedActionResponse_DA
    (eta : V) :
    linearizedActionResponse eta DA = (-2 : ℝ) • eta := by
  simp [linearizedActionResponse, DA]

/-- If the surviving fixed-point jet is J=-2 eta, the relative action mode maps exactly to J. -/
theorem linearizedActionResponse_relative_is_jet
    (eta J : V)
    (hJ : J = (-2 : ℝ) • eta) :
    linearizedActionResponse eta DA = J := by
  rw [linearizedActionResponse_DA, hJ]

end LinearizedActionResponse

/-! ## B. Strict monotonicity certificate for the boost defect -/

theorem boostDefect_hasDerivAt
    (qm qp sigma : ℝ) :
    HasDerivAt (boostDefect qm qp)
      (-2 * (Real.exp (-2 * sigma) * qm^2 +
        Real.exp (2 * sigma) * qp^2)) sigma := by
  have hm :
      HasDerivAt (fun s : ℝ => Real.exp (-2 * s))
        (-2 * Real.exp (-2 * sigma)) sigma := by
    convert ((hasDerivAt_id sigma).const_mul (-2)).exp using 1 <;> ring
  have hp :
      HasDerivAt (fun s : ℝ => Real.exp (2 * s))
        (2 * Real.exp (2 * sigma)) sigma := by
    convert ((hasDerivAt_id sigma).const_mul 2).exp using 1 <;> ring
  have h :=
    (hm.mul_const (qm^2)).sub (hp.mul_const (qp^2))
  convert h using 1 <;> ring

theorem boostDefect_derivative_negative
    (qm qp sigma : ℝ)
    (hqm : qm ≠ 0) (hqp : qp ≠ 0) :
    -2 * (Real.exp (-2 * sigma) * qm^2 +
      Real.exp (2 * sigma) * qp^2) < 0 := by
  have hqm2 : 0 < qm^2 := sq_pos_of_ne_zero hqm
  have hqp2 : 0 < qp^2 := sq_pos_of_ne_zero hqp
  have hm : 0 < Real.exp (-2 * sigma) * qm^2 :=
    mul_pos (Real.exp_pos _) hqm2
  have hp : 0 < Real.exp (2 * sigma) * qp^2 :=
    mul_pos (Real.exp_pos _) hqp2
  nlinarith

/-- At every point on the regular two-component branch the derivative of the boost defect is
strictly negative. -/
theorem boostDefect_has_negative_derivative
    (qm qp sigma : ℝ)
    (hqm : qm ≠ 0) (hqp : qp ≠ 0) :
    HasDerivAt (boostDefect qm qp)
      (-2 * (Real.exp (-2 * sigma) * qm^2 +
        Real.exp (2 * sigma) * qp^2)) sigma ∧
    -2 * (Real.exp (-2 * sigma) * qm^2 +
      Real.exp (2 * sigma) * qp^2) < 0 := by
  exact ⟨boostDefect_hasDerivAt qm qp sigma,
    boostDefect_derivative_negative qm qp sigma hqm hqp⟩

/-! ## C. Maxwell null boundary -/

/-- On the electromagnetic null-invariant locus, the arbitrary-frame mixed Maxwell stress
endomorphism squares to zero componentwise. -/
theorem emMixed_square_zero_on_null
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (hmag :
      b1^2 + b2^2 + b3^2 = e1^2 + e2^2 + e3^2)
    (hdot :
      e1*b1 + e2*b2 + e3*b3 = 0)
    (i j : Fin 4) :
    (∑ k : Fin 4,
      emMixed e1 e2 e3 b1 b2 b3 i k *
      emMixed e1 e2 e3 b1 b2 b3 k j) = 0 := by
  rw [emMixed_rainich_square]
  have hzero :
      emRainichScalar e1 e2 e3 b1 b2 b3 = 0 :=
    (emRainichScalar_eq_zero_iff
      e1 e2 e3 b1 b2 b3).2 ⟨hmag, hdot⟩
  simp [hzero]

/-- Off the null locus, the Rainich scalar is strictly positive and therefore nonzero. -/
theorem emRainichScalar_ne_zero_of_nonnull
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (hn : ¬ (b1^2 + b2^2 + b3^2 =
        e1^2 + e2^2 + e3^2 ∧
      e1*b1 + e2*b2 + e3*b3 = 0)) :
    emRainichScalar e1 e2 e3 b1 b2 b3 ≠ 0 :=
  ne_of_gt (emRainichScalar_pos_of_nonnull
    e1 e2 e3 b1 b2 b3 hn)

/-! ## D. Full Kerr--Newman curvature-to-Mino chain -/

theorem kerrNewman_curvature_to_mino
    (Q sig K chi omega dt dlam dtheta : ℝ)
    (hQ : Q ≠ 0)
    (hsig : 0 < sig)
    (hK : K = 4 * Q^4 / sig^4)
    (hchi : chi = Real.sqrt K)
    (homega : omega = Real.sqrt chi)
    (hclock : dtheta = omega * dt)
    (hmino : dlam = dt / sig) :
    dtheta = Real.sqrt 2 * |Q| * dlam := by
  have hcarrier :
      chi = 2 * Q^2 / sig^2 :=
    kerrNewman_chi_from_K Q sig K chi hsig hQ hK hchi
  exact kerrNewman_mino_from_invariant_clock
    Q sig chi omega dt dlam dtheta
    hQ hsig hcarrier homega hclock hmino

/-- The electromagnetic carrier collapses in the Q=0 specialization. -/
theorem kerrNewman_carrier_vacuum_limit
    (sig chi : ℝ)
    (hsig : sig ≠ 0)
    (hchi : chi = 2 * (0 : ℝ)^2 / sig^2) :
    chi = 0 := by
  rw [hchi]
  simp

/-- The corresponding positive square-root clock rate collapses with the carrier. -/
theorem kerrNewman_clock_vacuum_limit
    (chi omega : ℝ)
    (hchi : chi = 0)
    (homega : omega = Real.sqrt chi) :
    omega = 0 := by
  rw [homega, hchi]
  simp

end RelativeRest
