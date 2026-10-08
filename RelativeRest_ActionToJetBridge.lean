import RelativeRest_OneFile_Certificate
import RelativeRest_FieldDerivedJet

/-!
# Bridge the giant certificate to the independent Maxwell action-jet chain

A frequent logical gap in "action forces geometry" proofs is that the stress
appearing in the action derivative is not definitionally the same tensor as
the stress in the field equations or relative defect.

This file prevents that mismatch by using the EXISTING arbitrary-six-component
Maxwell field and EXISTING Maxwell metric-variation theorem in the parent
certificate. It constructs an actual potential first jet that realizes the
same F, then checks equality with the independently defined Gaussian-normalized
stress tensor, component by component.

Scope:
 * The potential construction is at ONE tangent-space jet; global potential
   existence still requires the Bianchi/closedness data.
 * The parent metric-variation theorem is local frame algebra, not a global
   integrated variational calculus.
 * The relative defect still requires the Einstein equation on shell.
 * No spacetime clock or Iyer-Wald current is inserted here.
-/

noncomputable section

open scoped BigOperators

namespace RelativeRest

/-- Local potential 1-jet realizing any given six-component Maxwell two-form:
    D_i A_j=F_ij/2 in the chosen orthonormal frame. -/
def generalMaxwellPotentialJet
    (Ex Ey Ez Bx By Bz : ℝ) : MaxwellAction.PotentialJet :=
  fun i j => (1 / 2 : ℝ) *
    generalMaxwellF Ex Ey Ez Bx By Bz i j

/-- No field strength need be independently supplied: differentiating the
    potential first jet gives exactly the six-component F in the existing file. -/
theorem generalMaxwellPotentialJet_fieldStrength
    (Ex Ey Ez Bx By Bz : ℝ) :
    MaxwellAction.fieldStrength
        (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz) =
      generalMaxwellF Ex Ey Ez Bx By Bz := by
  funext i j
  unfold MaxwellAction.fieldStrength generalMaxwellPotentialJet
  rw [generalMaxwellF_skew Ex Ey Ez Bx By Bz j i]
  ring

/-- The stress used by the parent action variation is the same covariant
    1/(4*pi)-normalized tensor obtained by explicit metric contractions
    from our F=dA, in every orthonormal-frame component. -/
theorem generalMaxwellStress_matches_action_variation_tensor
    (Ex Ey Ez Bx By Bz : ℝ)
    (i j : Fin 4) :
    MaxwellAction.physicalMaxwellStress
        (generalMaxwellF Ex Ey Ez Bx By Bz) i j =
      generalMaxwellStressCovFromF Ex Ey Ez Bx By Bz i j := by
  fin_cases i <;> fin_cases j <;>
    simp [MaxwellAction.physicalMaxwellStress,
      MaxwellAction.flatMaxwellStress,
      MaxwellAction.maxwellStress,
      MaxwellAction.maxwellQuadratic,
      MaxwellAction.maxwellContraction,
      MaxwellAction.etaCovariant,
      MaxwellAction.lorentzSign,
      generalMaxwellStressCovFromF,
      generalMaxwellStressFromF,
      generalMaxwellFsq,
      generalMaxwellF,
      principalMetricSign,
      Fin.sum_univ_four] <;>
    field_simp [ne_of_gt Real.pi_pos] <;>
    ring

/-- The original action's inverse-metric variation coefficient is exactly
    minus one half of the physical stress from this potential first jet.
    This bridges definitions rather than merely matching abstract symbols. -/
theorem generalMaxwellMetricVariation_from_potentialJet
    (Ex Ey Ez Bx By Bz : ℝ)
    (i j : Fin 4) :
    generalMaxwellMetricVariationCoeff Ex Ey Ez Bx By Bz i j =
      (-1 / 2 : ℝ) *
        MaxwellAction.physicalMaxwellStress
          (MaxwellAction.fieldStrength
            (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz)) i j := by
  rw [generalMaxwellPotentialJet_fieldStrength]
  rw [generalMaxwellMetricVariationCoeff_eq_neg_half_stress]
  rw [generalMaxwellStress_matches_action_variation_tensor]

/-- In the same normalization, the existing action-derived metric variation,
    the field stress, and the first surviving relative Einstein jet coincide. -/
theorem generalMaxwell_action_to_relativeJet
    (Ex Ey Ez Bx By Bz : ℝ)
    (G : MaxwellAction.Tensor44)
    (a b : Fin 4) :
    generalMaxwellMetricVariationCoeff Ex Ey Ez Bx By Bz a b =
        (-1 / 2 : ℝ) *
          MaxwellAction.physicalMaxwellStress
            (MaxwellAction.fieldStrength
              (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz)) a b ∧
    HasDerivAt
      (fun s : ℝ =>
        MaxwellAction.einsteinMaxwellRelativeResidual G
          (MaxwellAction.fieldStrength
            (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz)) s a b)
      (-16 * Real.pi *
        MaxwellAction.physicalMaxwellStress
          (MaxwellAction.fieldStrength
            (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz)) a b) 0 := by
  exact ⟨generalMaxwellMetricVariation_from_potentialJet
    Ex Ey Ez Bx By Bz a b,
    MaxwellAction.fieldDerivedResidual_hasDerivAt_zero
      G (MaxwellAction.fieldStrength
        (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz)) a b⟩

/-- An arbitrary nonzero electric component of F yields a physical positive
    energy witness and, ON SHELL, the unique relative action fixed point.
    The stress nonvanishing premise is no longer imported separately. -/
theorem generalMaxwell_potential_onShell_rest_unique
    (Ex Ey Ez Bx By Bz : ℝ)
    (G : MaxwellAction.Tensor44)
    (hEinstein : ∀ a b : Fin 4,
      G a b = 8 * Real.pi *
        MaxwellAction.physicalMaxwellStress
          (MaxwellAction.fieldStrength
            (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz)) a b)
    (hEx : Ex ≠ 0) (s : ℝ) :
    MaxwellAction.einsteinMaxwellRelativeResidual G
        (MaxwellAction.fieldStrength
          (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz)) s 0 0 = 0 ↔
      s = 0 := by
  apply MaxwellAction.potentialJet_forces_relative_rest
    G (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz) hEinstein
  rw [generalMaxwellPotentialJet_fieldStrength]
  simpa [generalMaxwellF] using hEx

end RelativeRest
