import RelativeRest_ActionToJetBridge

/-!
# All-order relative Einstein--Maxwell jet from the action-defined Maxwell stress

The Einstein equation on shell, constant metric homothety and the two independent
action-sector characters lead to a projectively normalized residual.
This module proves its oddness, fixed-point uniqueness, all even/odd iterated
normal derivatives and Ricci identification by REUSING THE FULL PARENT
CERTIFICATE's proven scalar/functional derivative identities.

No independent normal-jet formula or parity condition is assumed.
The Einstein equation is explicitly supplied as a premise of the on-shell
theorems: the regular fields must be actual solutions, not arbitrary 4x4 data.
-/

noncomputable section
open scoped BigOperators

namespace RelativeRest
namespace MaxwellAction

/-- The common-character-removed field equation residual.  The factor
    exp(-s) is fixed by the reciprocal gravity/Maxwell characters, not by
    a freely chosen clock normalization. -/
def oddRelativeResidual
    (G F : Tensor44) (a b : Fin 4) : ℝ → ℝ :=
  fun s => Real.exp (-s) * einsteinMaxwellRelativeResidual G F s a b

/-- Exact on-shell identification with the *existing action-derived scalar
    defect* in the 35k-line certificate. -/
theorem oddRelativeResidual_eq_actionDefect
    (G F : Tensor44)
    (hEinstein : ∀ a b : Fin 4,
      G a b = 8 * Real.pi * physicalMaxwellStress F a b)
    (a b : Fin 4) :
    oddRelativeResidual G F =
      defect (physicalMaxwellStress F a b) := by
  funext s
  exact defect_from_on_shell_equation
    (G a b) (physicalMaxwellStress F a b) s (hEinstein a b)

/-- Antisymmetry under exchange of gravitational and electromagnetic
    characters is now a theorem for the field-derived on-shell tensor. -/
theorem oddRelativeResidual_exchange
    (G F : Tensor44)
    (hEinstein : ∀ a b : Fin 4,
      G a b = 8 * Real.pi * physicalMaxwellStress F a b)
    (a b : Fin 4) (s : ℝ) :
    oddRelativeResidual G F a b (-s) =
      -oddRelativeResidual G F a b s := by
  rw [oddRelativeResidual_eq_actionDefect G F hEinstein,
    oddRelativeResidual_eq_actionDefect G F hEinstein]
  simp [defect, Real.sinh_neg]

/-- The unique fixed point for every nonzero stress component follows
    without a separate exchange-rest axiom. -/
theorem oddRelativeResidual_zero_iff_rest
    (G F : Tensor44)
    (hEinstein : ∀ a b : Fin 4,
      G a b = 8 * Real.pi * physicalMaxwellStress F a b)
    (a b : Fin 4)
    (hT : physicalMaxwellStress F a b ≠ 0) (s : ℝ) :
    oddRelativeResidual G F a b s = 0 ↔ s = 0 := by
  rw [oddRelativeResidual_eq_actionDefect G F hEinstein]
  exact defect_eq_zero_iff (physicalMaxwellStress F a b) s hT

/-- The action-normal derivative at relative rest equals -16*pi*T.
    This does not require declaring the normal jet as an input. -/
theorem oddRelativeResidual_firstJet_from_action
    (G F : Tensor44)
    (hEinstein : ∀ a b : Fin 4,
      G a b = 8 * Real.pi * physicalMaxwellStress F a b)
    (a b : Fin 4) :
    HasDerivAt (oddRelativeResidual G F a b)
      (-16 * Real.pi * physicalMaxwellStress F a b) 0 := by
  rw [oddRelativeResidual_eq_actionDefect G F hEinstein]
  exact defect_hasDerivAt_zero (physicalMaxwellStress F a b)

/-- All even normal derivatives vanish, while all odd ones equal the
    *same field-defined first jet*. This is derived using the parent's
    actual iterated derivative theorem for sinh, not a parity assertion. -/
theorem oddRelativeResidual_all_normal_jets
    (G F : Tensor44)
    (hEinstein : ∀ a b : Fin 4,
      G a b = 8 * Real.pi * physicalMaxwellStress F a b)
    (a b : Fin 4) (n : ℕ) :
    iteratedDeriv (2*n) (oddRelativeResidual G F a b) 0 = 0 ∧
    iteratedDeriv (2*n+1) (oddRelativeResidual G F a b) 0 =
      -16 * Real.pi * physicalMaxwellStress F a b := by
  have hfun :
      oddRelativeResidual G F a b =
        carrierOdd (8 * Real.pi * physicalMaxwellStress F a b) := by
    rw [oddRelativeResidual_eq_actionDefect G F hEinstein]
    funext s
    simp only [defect, carrierOdd]
    ring
  rw [hfun]
  rcases carrierOdd_full_jet_parity
      (8 * Real.pi * physicalMaxwellStress F a b) n with
    ⟨heven, hodd⟩
  refine ⟨heven, ?_⟩
  calc
    iteratedDeriv (2*n+1)
        (carrierOdd (8 * Real.pi * physicalMaxwellStress F a b)) 0 =
        -2 * (8 * Real.pi * physicalMaxwellStress F a b) := hodd
    _ = -16 * Real.pi * physicalMaxwellStress F a b := by ring

/-- The geometric identification J=-2 Ric becomes a consequence of the
    on-shell Einstein equation, the traceless Maxwell source, and the
    *definition* of the Einstein tensor. The scalar-curvature identity
    itself is still a geometric input, not hidden in a field named Ric. -/
theorem oddRelativeResidual_firstJet_eq_minusTwoRicci
    (G Ric F : Tensor44) (R : ℝ)
    (hEinstein : ∀ a b : Fin 4,
      G a b = 8 * Real.pi * physicalMaxwellStress F a b)
    (hRelation : ∀ a b : Fin 4,
      G a b = Ric a b - (1 / 2 : ℝ) * etaCovariant a b * R)
    (hTrace : -R =
      8 * Real.pi *
        (∑ a : Fin 4, lorentzSign a * physicalMaxwellStress F a a))
    (a b : Fin 4) :
    deriv (oddRelativeResidual G F a b) 0 = -2 * Ric a b := by
  have hzero : R = 0 :=
    onShellEinsteinMaxwell_scalarCurvature_zero F R hTrace
  have hRic :=
    ricciEqualsMaxwellSource_onShell
      G Ric F R hEinstein hRelation hzero a b
  rw [(oddRelativeResidual_firstJet_from_action
    G F hEinstein a b).deriv]
  rw [hRic]
  ring

/-! ### Remove the intermediate Einstein equation hypothesis from the final jet theorem -/

/-- Convert the action's mixed Einstein tensor into its covariant components
    using the same orthonormal-frame metric used in the displayed action. -/
def covariantEinsteinFromActionMixed
    (Gmixed : Tensor44) : Tensor44 :=
  fun i j => principalMetricSign i * Gmixed i j

/-- The parent certificate's *explicit Einstein--Maxwell action metric Euler
    derivative* vanishing implies the physical covariant on-shell equation
    for the SAME potential jet. No Einstein-equation hypothesis is inserted. -/
theorem actionBulkStationarity_forces_covariantEinsteinEquation
    (Gmixed : Tensor44)
    (Ex Ey Ez Bx By Bz : ℝ)
    (hstationary : ∀ i j : Fin 4,
      generalEinsteinMaxwellMetricVariationCoeff
        Gmixed Ex Ey Ez Bx By Bz i j = 0)
    (i j : Fin 4) :
    covariantEinsteinFromActionMixed Gmixed i j =
      8 * Real.pi *
        physicalMaxwellStress
          (fieldStrength
            (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz)) i j := by
  have hEinsteinMixed :
      Gmixed i j =
        8 * Real.pi *
          generalMaxwellStressFromF Ex Ey Ez Bx By Bz i j :=
    (generalEinsteinMaxwellMetricVariationCoeff_eq_zero_iff
      Gmixed Ex Ey Ez Bx By Bz i j).mp (hstationary i j)
  rw [generalMaxwellPotentialJet_fieldStrength]
  rw [generalMaxwellStress_matches_action_variation_tensor]
  unfold covariantEinsteinFromActionMixed generalMaxwellStressCovFromF
  rw [hEinsteinMixed]
  ring

/-- Action-stationarity-to-normal-jet: one actual input, namely the
    vanishing metric Euler coefficients from the displayed Einstein--Maxwell
    action, is enough to derive the entire even/odd normal-jet tower. -/
theorem actionBulkStationarity_forces_all_oddTensorJets
    (Gmixed : Tensor44)
    (Ex Ey Ez Bx By Bz : ℝ)
    (hstationary : ∀ i j : Fin 4,
      generalEinsteinMaxwellMetricVariationCoeff
        Gmixed Ex Ey Ez Bx By Bz i j = 0)
    (a b : Fin 4) (n : ℕ) :
    iteratedDeriv (2*n)
        (oddRelativeResidual
          (covariantEinsteinFromActionMixed Gmixed)
          (fieldStrength
            (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz)) a b) 0 = 0 ∧
    iteratedDeriv (2*n+1)
        (oddRelativeResidual
          (covariantEinsteinFromActionMixed Gmixed)
          (fieldStrength
            (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz)) a b) 0 =
      -16 * Real.pi *
        physicalMaxwellStress
          (fieldStrength
            (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz)) a b := by
  have hEinstein : ∀ i j : Fin 4,
      covariantEinsteinFromActionMixed Gmixed i j =
        8 * Real.pi *
          physicalMaxwellStress
            (fieldStrength
              (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz)) i j := by
    intro i j
    exact actionBulkStationarity_forces_covariantEinsteinEquation
      Gmixed Ex Ey Ez Bx By Bz hstationary i j
  exact oddRelativeResidual_all_normal_jets
    (covariantEinsteinFromActionMixed Gmixed)
    (fieldStrength
      (generalMaxwellPotentialJet Ex Ey Ez Bx By Bz))
    hEinstein a b n

end MaxwellAction
end RelativeRest
