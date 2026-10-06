import RelativeRest_DeepPass34

/-!
# Relative Rest: deep forced pass 35

Promote the arbitrary-frame Maxwell Rainich identity to an actual linear endomorphism.

The component theorem from DeepPass34 says that the fixed-point jet matrix squares to the Maxwell
invariant norm times the identity matrix.  Mathlib's Matrix.mulVecLin turns this into composition
of linear maps.  On the non-null branch the positive carrier magnitude is nonzero, so the
normalized field-derived jet S=chi^{-1}J is an involution and its canonical P_± projectors follow.

No abstract Rainich-square hypothesis is supplied in this construction.
-/

noncomputable section

open Function Set
open scoped BigOperators

namespace RelativeRest

/-- Matrix-level fixed-point Rainich identity. -/
theorem emJetMixed_matrix_square
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    emJetMixed e1 e2 e3 b1 b2 b3 *
        emJetMixed e1 e2 e3 b1 b2 b3 =
      (emInvariantNormSq e1 e2 e3 b1 b2 b3) •
        (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  rw [Matrix.mul_apply,
    emJetMixed_rainich_square
      e1 e2 e3 b1 b2 b3 i j]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- The fixed-point Maxwell jet as a genuine endomorphism of the frame vector space. -/
def emJetEndomorphism
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    Vec4 →ₗ[ℝ] Vec4 :=
  Matrix.mulVecLin
    (emJetMixed e1 e2 e3 b1 b2 b3)

/-- Composition of the field-derived jet with itself is the invariant scalar times identity. -/
theorem emJetEndomorphism_rainich_square
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    (emJetEndomorphism
      e1 e2 e3 b1 b2 b3).comp
      (emJetEndomorphism
        e1 e2 e3 b1 b2 b3) =
      (emInvariantNormSq
        e1 e2 e3 b1 b2 b3) •
        LinearMap.id := by
  unfold emJetEndomorphism
  rw [← Matrix.mulVecLin_mul,
    emJetMixed_matrix_square]
  apply LinearMap.ext
  intro v
  change
    ((emInvariantNormSq
        e1 e2 e3 b1 b2 b3) •
      (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ v =
      (emInvariantNormSq
        e1 e2 e3 b1 b2 b3) • v
  rw [smul_mulVec, one_mulVec]

/-- The normalized fixed-point Maxwell jet. -/
def emNormalizedJet
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    Vec4 →ₗ[ℝ] Vec4 :=
  ((emCarrierMagnitude
      e1 e2 e3 b1 b2 b3)⁻¹) •
    emJetEndomorphism
      e1 e2 e3 b1 b2 b3

/-- On the non-null Maxwell stratum the field-derived normalized jet is an involution. -/
theorem emNormalizedJet_involution
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (hn : ¬ (b1^2 + b2^2 + b3^2 =
        e1^2 + e2^2 + e3^2 ∧
      e1*b1 + e2*b2 + e3*b3 = 0)) :
    (emNormalizedJet
      e1 e2 e3 b1 b2 b3).comp
      (emNormalizedJet
        e1 e2 e3 b1 b2 b3) =
      LinearMap.id := by
  unfold emNormalizedJet
  apply normalized_involution
    (emJetEndomorphism
      e1 e2 e3 b1 b2 b3)
    (emCarrierMagnitude
      e1 e2 e3 b1 b2 b3)
  · exact ne_of_gt
      (emCarrierMagnitude_pos_of_nonnull
        e1 e2 e3 b1 b2 b3 hn)
  · rw [emJetEndomorphism_rainich_square,
      emCarrierMagnitude_sq]

/-- The plus projector produced directly from Maxwell data has eigenvalue +1. -/
theorem emPrincipalProjPlus_eigen
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (hn : ¬ (b1^2 + b2^2 + b3^2 =
        e1^2 + e2^2 + e3^2 ∧
      e1*b1 + e2*b2 + e3*b3 = 0))
    (v : Vec4) :
    emNormalizedJet e1 e2 e3 b1 b2 b3
        (involutionProjPlus
          (emNormalizedJet
            e1 e2 e3 b1 b2 b3) v) =
      involutionProjPlus
        (emNormalizedJet
          e1 e2 e3 b1 b2 b3) v := by
  exact involution_plus_eigen
    (emNormalizedJet
      e1 e2 e3 b1 b2 b3)
    (emNormalizedJet_involution
      e1 e2 e3 b1 b2 b3 hn)
    v

/-- The minus projector produced directly from Maxwell data has eigenvalue -1. -/
theorem emPrincipalProjMinus_eigen
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (hn : ¬ (b1^2 + b2^2 + b3^2 =
        e1^2 + e2^2 + e3^2 ∧
      e1*b1 + e2*b2 + e3*b3 = 0))
    (v : Vec4) :
    emNormalizedJet e1 e2 e3 b1 b2 b3
        (involutionProjMinus
          (emNormalizedJet
            e1 e2 e3 b1 b2 b3) v) =
      - involutionProjMinus
        (emNormalizedJet
          e1 e2 e3 b1 b2 b3) v := by
  exact involution_minus_eigen
    (emNormalizedJet
      e1 e2 e3 b1 b2 b3)
    (emNormalizedJet_involution
      e1 e2 e3 b1 b2 b3 hn)
    v

end RelativeRest
