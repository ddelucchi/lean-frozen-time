import RelativeRest_ActionOddTensorJet
import RelativeRest_SynchronizationScope

/-!
# Strict Lean kernel dependency audit

This module imports the entire 35,861-line certificate through the new bridge,
then interrogates each new logical link with #print axioms.

Passing this file in Lean verifies that every referenced declaration is compiled.
The #print axioms output must be inspected: Mathlib may use classical/quotient
principles, but no project-local theorem is to be accepted as an assumed axiom.
A text scan for the string "sorry" is NOT a substitute for these checks.
-/

#print axioms RelativeRest.MaxwellAction.fieldStrength_gauge_invariant
#print axioms RelativeRest.MaxwellAction.density_gauge_invariant
#print axioms RelativeRest.MaxwellAction.quadraticDensity_exact_increment
#print axioms RelativeRest.MaxwellAction.maxwellStress_scale
#print axioms RelativeRest.MaxwellAction.homotheticMaxwellStress_eq
#print axioms RelativeRest.MaxwellAction.flatMaxwellStress_tracefree
#print axioms RelativeRest.MaxwellAction.physicalMaxwellStress_tracefree
#print axioms RelativeRest.MaxwellAction.potentialJet_energy_density_formula
#print axioms RelativeRest.MaxwellAction.fieldDerivedResidual_hasDerivAt_zero
#print axioms RelativeRest.MaxwellAction.oddRelativeResidual_all_normal_jets
#print axioms RelativeRest.MaxwellAction.oddRelativeResidual_firstJet_eq_minusTwoRicci
#print axioms RelativeRest.MaxwellAction.actionBulkStationarity_forces_covariantEinsteinEquation
#print axioms RelativeRest.MaxwellAction.actionBulkStationarity_forces_all_oddTensorJets
#print axioms RelativeRest.MaxwellAction.actionBulkStationarity_nonzeroElectric_forces_rest
#print axioms RelativeRest.generalMaxwellPotentialJet_fieldStrength
#print axioms RelativeRest.generalMaxwellStress_matches_action_variation_tensor
#print axioms RelativeRest.generalMaxwellMetricVariation_from_potentialJet
#print axioms RelativeRest.generalMaxwell_action_to_relativeJet
#print axioms RelativeRest.IntrinsicBoostScope.no_nonzero_vector_fixed_by_nonzero_lorentz_boost
#print axioms RelativeRest.SynchronizationScope.curl_and_reference_do_not_force_unique_correction
#print axioms RelativeRest.SynchronizationScope.optical_gradient_forces_unique_correction

/-- Direct cross-check: the action-stationary field produces both a unique
    rest-point and an all-orders fixed-point jet without a standalone
    on-shell Einstein-tensor input. -/
theorem actionStationary_relativeRest_and_jet_audit
    (Gmixed : RelativeRest.MaxwellAction.Tensor44)
    (Ex Ey Ez Bx By Bz : ℝ)
    (hstationary : ∀ i j : Fin 4,
      RelativeRest.generalEinsteinMaxwellMetricVariationCoeff
        Gmixed Ex Ey Ez Bx By Bz i j = 0)
    (hEx : Ex ≠ 0)
    (s : ℝ) (a b : Fin 4) (n : ℕ) :
    (RelativeRest.MaxwellAction.oddRelativeResidual
        (RelativeRest.MaxwellAction.covariantEinsteinFromActionMixed Gmixed)
        (RelativeRest.MaxwellAction.fieldStrength
          (RelativeRest.generalMaxwellPotentialJet Ex Ey Ez Bx By Bz))
        0 0 s = 0 ↔ s = 0) ∧
    (iteratedDeriv (2*n)
        (RelativeRest.MaxwellAction.oddRelativeResidual
          (RelativeRest.MaxwellAction.covariantEinsteinFromActionMixed Gmixed)
          (RelativeRest.MaxwellAction.fieldStrength
            (RelativeRest.generalMaxwellPotentialJet Ex Ey Ez Bx By Bz))
          a b) 0 = 0) := by
  exact ⟨
    RelativeRest.MaxwellAction.actionBulkStationarity_nonzeroElectric_forces_rest
      Gmixed Ex Ey Ez Bx By Bz hstationary hEx s,
    (RelativeRest.MaxwellAction.actionBulkStationarity_forces_all_oddTensorJets
      Gmixed Ex Ey Ez Bx By Bz hstationary a b n).1⟩

#print axioms actionStationary_relativeRest_and_jet_audit
