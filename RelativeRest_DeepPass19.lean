import RelativeRest_DeepPass18

/-!
# Relative Rest: deep forced pass 19

Join the two Kerr--Newman specialization arms.

The field-derived radial carrier already forces the normalized Carter observer, while the same
curvature scalar fixes the invariant clock rate and hence the Mino parameter.  This file packages
those statements into one end-to-end theorem on the regular exterior branch.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-- On the regular Kerr--Newman branch, the field-derived balance simultaneously fixes the
normalized Carter frame, its angular velocity, and the Mino-normalized intrinsic clock. -/
theorem kerrNewman_field_forces_Carter_Mino
    (r M a Q theta sigma K chi omega dt dlam dtheta : ℝ)
    (hr : r ≠ 0)
    (hQ : Q ≠ 0)
    (hA : knA r a ≠ 0)
    (hbal :
      boostDefect
        (knRadialResponseMinus r M a Q theta)
        (knRadialResponsePlus r M a Q theta)
        sigma = 0)
    (hprod : 0 < Sigma r a theta * Delta r M a Q)
    (hK :
      K = 4 * Q^4 / (Sigma r a theta)^4)
    (hchi : chi = Real.sqrt K)
    (homega : omega = Real.sqrt chi)
    (hclock : dtheta = omega * dt)
    (hmino : dlam = dt / Sigma r a theta) :
    knBalancedT r a sigma = knA r a ∧
    knBalancedR r M a Q sigma = 0 ∧
    knBalancedPhi a sigma = a ∧
    knTRPhiNorm r M a Q theta
      (knA r a / knCarterNormFactor r M a Q theta)
      0
      (a / knCarterNormFactor r M a Q theta) = -1 ∧
    (a / knCarterNormFactor r M a Q theta) /
      (knA r a / knCarterNormFactor r M a Q theta) =
        a / knA r a ∧
    dtheta = Real.sqrt 2 * |Q| * dlam := by
  have hsig_nonneg : 0 ≤ Sigma r a theta := by
    unfold Sigma
    positivity
  have hsig_ne : Sigma r a theta ≠ 0 := by
    intro hs
    rw [hs, zero_mul] at hprod
    linarith
  have hsig_pos : 0 < Sigma r a theta :=
    lt_of_le_of_ne hsig_nonneg (Ne.symm hsig_ne)
  rcases
      knFieldCarrier_Carter_observer_certificate
        r M a Q theta sigma hr hbal hprod with
    ⟨ht, hrad, hphi, hunit⟩
  have hang :
      (a / knCarterNormFactor r M a Q theta) /
          (knA r a / knCarterNormFactor r M a Q theta) =
        a / knA r a :=
    knCarter_angular_velocity r M a Q theta hprod hA
  have hminoClock :
      dtheta = Real.sqrt 2 * |Q| * dlam :=
    kerrNewman_curvature_to_mino
      Q (Sigma r a theta) K chi omega dt dlam dtheta
      hQ hsig_pos hK hchi homega hclock hmino
  exact ⟨ht, hrad, hphi, hunit, hang, hminoClock⟩

end RelativeRest
