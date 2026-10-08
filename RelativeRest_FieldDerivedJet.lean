import RelativeRest_Maxwell_StressScaling

/-!
# Relative Einstein--Maxwell residual from a field-defined stress

This layer joins a genuinely tensor-defined Maxwell stress to the relative
Einstein-equation defect and its first surviving rapidity derivative.

The Einstein tensor G_ab is EXPLICITLY an input: its identity with the
field-defined Maxwell stress is the on-shell Einstein equation. The constant
homothety invariance of G_ab is differential-geometric, not inferred from
pointwise tensor algebra. Under those exact hypotheses, however, no fixed-
point or normal derivative identity is assumed separately.

The target formula is J_ab = -16*pi T_ab, with T_ab carrying the ordinary
1/(4*pi) normalization when necessary.
-/

noncomputable section

open scoped BigOperators

namespace RelativeRest
namespace MaxwellAction

/-- With matter stress S_ab normalized so that G_ab=8*pi*S_ab,
    the relative scaled Einstein equation has the tensor-valued defect
    G_ab - exp(2s)*8*pi*S_ab. -/
def einsteinMaxwellRelativeResidual
    (G F : Tensor44) (s : ℝ) : Tensor44 :=
  fun a b =>
    G a b - Real.exp (2*s) * (8 * Real.pi * physicalMaxwellStress F a b)

/-- If G=8*pi*S, the relative defect vanishes at the rest point s=0. -/
theorem fieldDerivedResidual_zero_at_rest
    (G F : Tensor44)
    (hEinstein : ∀ a b : Fin 4,
      G a b = 8 * Real.pi * physicalMaxwellStress F a b)
    (a b : Fin 4) :
    einsteinMaxwellRelativeResidual G F 0 a b = 0 := by
  simp [einsteinMaxwellRelativeResidual, hEinstein a b]

/-- More strongly, a single nonzero Maxwell stress component forces the
    scaled Einstein residual to have its only zero at s=0. -/
theorem fieldDerivedResidual_zero_iff_rest
    (G F : Tensor44)
    (hEinstein : ∀ a b : Fin 4,
      G a b = 8 * Real.pi * physicalMaxwellStress F a b)
    (a b : Fin 4)
    (hT : physicalMaxwellStress F a b ≠ 0)
    (s : ℝ) :
    einsteinMaxwellRelativeResidual G F s a b = 0 ↔ s = 0 := by
  constructor
  · intro h
    have hscaled :
        (8 * Real.pi * physicalMaxwellStress F a b) *
          (1 - Real.exp (2*s)) = 0 := by
      have hh := h
      dsimp [einsteinMaxwellRelativeResidual] at hh
      rw [hEinstein a b] at hh
      nlinarith [hh]
    have hnormal :
        8 * Real.pi * physicalMaxwellStress F a b ≠ 0 := by
      exact mul_ne_zero (by positivity) hT
    have he : Real.exp (2*s) = 1 := by
      rcases mul_eq_zero.mp hscaled with hbad | hrest
      · exact False.elim (hnormal hbad)
      · linarith
    have hs : 2*s = 0 := Real.exp_eq_one_iff.mp he
    linarith
  · intro hs
    subst s
    exact fieldDerivedResidual_zero_at_rest G F hEinstein a b

/-- No separate J=-16*pi*S postulate: it is the derivative of the
    field-defined Einstein equation defect under the relative action orbit. -/
theorem fieldDerivedResidual_hasDerivAt_zero
    (G F : Tensor44) (a b : Fin 4) :
    HasDerivAt
      (fun s : ℝ => einsteinMaxwellRelativeResidual G F s a b)
      (-16 * Real.pi * physicalMaxwellStress F a b) 0 := by
  have hexp :
      HasDerivAt (fun s : ℝ => Real.exp (2*s)) 2 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul 2).exp using 1 <;>
      norm_num
  have hconst :
      HasDerivAt (fun _ : ℝ => G a b) 0 0 := by
    exact hasDerivAt_const 0 (G a b)
  have h :=
    hconst.sub
      (hexp.mul_const
        (8 * Real.pi * physicalMaxwellStress F a b))
  convert h using 1 <;>
    simp [einsteinMaxwellRelativeResidual] <;> ring

/-- The affine frame-defined Maxwell stress has zero mixed trace in D=4. -/
theorem flatMaxwellStress_tracefree (F : Tensor44) :
    (∑ a : Fin 4,
      lorentzSign a * flatMaxwellStress F a a) = 0 := by
  simp [flatMaxwellStress, maxwellStress, maxwellQuadratic,
    maxwellContraction, etaCovariant, lorentzSign, Fin.sum_univ_four]
  ring

/-- Restoring 1/(4*pi) does not change Maxwell tracelessness. -/
theorem physicalMaxwellStress_tracefree (F : Tensor44) :
    (∑ a : Fin 4,
      lorentzSign a * physicalMaxwellStress F a a) = 0 := by
  calc
    (∑ a : Fin 4,
      lorentzSign a * physicalMaxwellStress F a a) =
        (1 / (4 * Real.pi)) *
          (∑ a : Fin 4,
            lorentzSign a * flatMaxwellStress F a a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      unfold physicalMaxwellStress
      ring
    _ = 0 := by rw [flatMaxwellStress_tracefree F]; ring

/-- Contracting the 4D Einstein equation with the inverse metric yields
    -R=8*pi*tr(T). Trace-free Maxwell stress therefore forces R=0.
    The Einstein trace relation itself is explicitly an upstream hypothesis. -/
theorem onShellEinsteinMaxwell_scalarCurvature_zero
    (F : Tensor44) (R : ℝ)
    (htrace : -R =
      8 * Real.pi *
        (∑ a : Fin 4,
          lorentzSign a * physicalMaxwellStress F a a)) :
    R = 0 := by
  rw [physicalMaxwellStress_tracefree F] at htrace
  linarith

/-! ### Eliminate the nonzero-stress witness using the Maxwell potential -/

/-- Six independent components of F=dA contribute positive squares to the
    electromagnetic energy density measured by the orthonormal time observer. -/
def potentialJetEnergySquare (D : PotentialJet) : ℝ :=
    (fieldStrength D 0 1)^2 +
    (fieldStrength D 0 2)^2 +
    (fieldStrength D 0 3)^2 +
    (fieldStrength D 1 2)^2 +
    (fieldStrength D 1 3)^2 +
    (fieldStrength D 2 3)^2

/-- All six squares are nonnegative for any real potential first jet. -/
theorem potentialJetEnergySquare_nonneg (D : PotentialJet) :
    0 ≤ potentialJetEnergySquare D := by
  unfold potentialJetEnergySquare
  positivity

/-- Exact Maxwell T_00 positivity formula, derived from the field-strength
    tensor and the Gaussian-normalized stress contraction. -/
theorem potentialJet_energy_density_formula (D : PotentialJet) :
    physicalMaxwellStress (fieldStrength D) 0 0 =
      potentialJetEnergySquare D / (8 * Real.pi) := by
  simp [physicalMaxwellStress, flatMaxwellStress, maxwellStress,
    maxwellQuadratic, maxwellContraction, etaCovariant,
    lorentzSign, potentialJetEnergySquare, fieldStrength,
    Fin.sum_univ_four]
  field_simp [ne_of_gt Real.pi_pos]
  ring

/-- A nonzero electric component already provides a constructive nonzero
    stress witness; the higher-energy/magnetic cases are analogous. -/
theorem nonzero_electric_potential_jet_forces_stress_witness
    (D : PotentialJet)
    (hE : fieldStrength D 0 1 ≠ 0) :
    physicalMaxwellStress (fieldStrength D) 0 0 ≠ 0 := by
  have hE2 : 0 < (fieldStrength D 0 1)^2 :=
    sq_pos_of_ne_zero hE
  have hS : 0 < potentialJetEnergySquare D := by
    unfold potentialJetEnergySquare
    nlinarith [sq_nonneg (fieldStrength D 0 2),
      sq_nonneg (fieldStrength D 0 3),
      sq_nonneg (fieldStrength D 1 2),
      sq_nonneg (fieldStrength D 1 3),
      sq_nonneg (fieldStrength D 2 3)]
  rw [potentialJet_energy_density_formula]
  exact ne_of_gt (div_pos hS (by positivity))

/-- The relative fixed point is forced directly by a nonzero potential jet,
    without supplying Maxwell stress nonvanishing as a separate hypothesis. -/
theorem potentialJet_forces_relative_rest
    (G : Tensor44) (D : PotentialJet)
    (hEinstein : ∀ a b : Fin 4,
      G a b =
        8 * Real.pi *
          physicalMaxwellStress (fieldStrength D) a b)
    (hE : fieldStrength D 0 1 ≠ 0)
    (s : ℝ) :
    einsteinMaxwellRelativeResidual G (fieldStrength D) s 0 0 = 0 ↔
      s = 0 := by
  exact fieldDerivedResidual_zero_iff_rest
    G (fieldStrength D) hEinstein 0 0
      (nonzero_electric_potential_jet_forces_stress_witness D hE) s

/-- Maxwell gauge shifts of the potential leave the full on-shell relative
    Einstein defect unchanged for every rapidity. -/
theorem relativeResidual_gauge_invariant
    (G : Tensor44) (D H : PotentialJet)
    (hH : ∀ a b : Fin 4, H a b = H b a)
    (s : ℝ) :
    einsteinMaxwellRelativeResidual
        G (fieldStrength (fun a b => D a b + H a b)) s =
      einsteinMaxwellRelativeResidual G (fieldStrength D) s := by
  rw [fieldStrength_gauge_invariant D H hH]

/-- Under the on-shell equality G=8*pi*S and R=0, the Ricci tensor
    equals the field-derived source in the orthonormal frame. -/
theorem ricciEqualsMaxwellSource_onShell
    (G Ric F : Tensor44) (R : ℝ)
    (hEinstein : ∀ a b : Fin 4,
      G a b = 8 * Real.pi * physicalMaxwellStress F a b)
    (hRelation : ∀ a b : Fin 4,
      G a b = Ric a b - (1 / 2 : ℝ) * etaCovariant a b * R)
    (hScalar : R = 0)
    (a b : Fin 4) :
    Ric a b = 8 * Real.pi * physicalMaxwellStress F a b := by
  have hg := hRelation a b
  rw [hScalar] at hg
  simp at hg
  rw [hEinstein a b] at hg
  linarith

/-! ### Exact degenerate boundary: the vacuum does not fix relative scale -/

/-- In the vanishing Maxwell-field sector the relative Einstein defect is zero
    for every rapidity when the Einstein tensor also vanishes. Thus a unique
    relative fixed point requires a nonzero matter carrier. -/
theorem vacuumRelativeResidual_identically_zero
    (s : ℝ) (a b : Fin 4) :
    einsteinMaxwellRelativeResidual
        (fun _ _ => (0 : ℝ))
        (fun _ _ => (0 : ℝ)) s a b = 0 := by
  simp [einsteinMaxwellRelativeResidual, physicalMaxwellStress,
    flatMaxwellStress, maxwellStress, maxwellQuadratic,
    maxwellContraction]

/-- An explicit non-rest fixed point exists in the vacuum sector. -/
theorem vacuumRelativeResidual_has_nonrest_zero :
    ∃ s : ℝ, s ≠ 0 ∧
      ∀ a b : Fin 4,
        einsteinMaxwellRelativeResidual
          (fun _ _ => (0 : ℝ))
          (fun _ _ => (0 : ℝ)) s a b = 0 := by
  refine ⟨1, by norm_num, ?_⟩
  intro a b
  exact vacuumRelativeResidual_identically_zero 1 a b

end MaxwellAction
end RelativeRest
