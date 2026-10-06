import RelativeRest_DeepPass35

/-!
# Relative Rest: deep forced pass 36

Derive Lorentzian self-adjointness and orthogonality of the Maxwell principal planes.

Use the explicit orthonormal-frame Minkowski form diag(-1,+1,+1,+1).  The mixed Maxwell stress,
and hence the fixed-point jet J=-4T, is self-adjoint for this form because lowering its first index
recovers a symmetric stress tensor.  Here that fact is verified directly from the arbitrary-frame
E,B components.

Combined with the field-derived Rainich involution, the P_+ and P_- images are therefore
orthogonal principal planes without an abstract self-adjointness hypothesis.
-/

noncomputable section

open Function Set
open scoped BigOperators

namespace RelativeRest

/-- Minkowski bilinear form in the orthonormal frame used for emMixed. -/
def minkowskiBilin :
    Vec4 →ₗ[ℝ] Vec4 →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y =>
        -(x 0 * y 0) +
          x 1 * y 1 +
          x 2 * y 2 +
          x 3 * y 3
      map_add' := by
        intro y z
        simp
        ring
      map_smul' := by
        intro c y
        simp
        ring }
  map_add' := by
    intro x y
    ext z
    simp
    ring
  map_smul' := by
    intro c x
    ext y
    simp
    ring

theorem minkowskiBilin_symmetric
    (x y : Vec4) :
    minkowskiBilin x y =
      minkowskiBilin y x := by
  unfold minkowskiBilin
  ring

/-- Direct arbitrary-frame check that the fixed-point Maxwell jet is self-adjoint for the
Lorentzian metric. -/
theorem emJetEndomorphism_selfadjoint
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (x y : Vec4) :
    minkowskiBilin x
        (emJetEndomorphism
          e1 e2 e3 b1 b2 b3 y) =
      minkowskiBilin
        (emJetEndomorphism
          e1 e2 e3 b1 b2 b3 x) y := by
  simp [minkowskiBilin, emJetEndomorphism,
    Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four,
    emJetMixed, emMixed, emEnergy,
    emPoynting1, emPoynting2, emPoynting3]
  ring

/-- The normalized field-derived carrier remains Lorentz-self-adjoint. -/
theorem emNormalizedJet_selfadjoint
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (x y : Vec4) :
    minkowskiBilin x
        (emNormalizedJet
          e1 e2 e3 b1 b2 b3 y) =
      minkowskiBilin
        (emNormalizedJet
          e1 e2 e3 b1 b2 b3 x) y := by
  unfold emNormalizedJet
  simp [map_smul,
    emJetEndomorphism_selfadjoint
      e1 e2 e3 b1 b2 b3 x y]

/-- The two Maxwell/Rainich principal planes are orthogonal on the non-null branch. -/
theorem emPrincipalPlanes_orthogonal
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (hn : ¬ (b1^2 + b2^2 + b3^2 =
        e1^2 + e2^2 + e3^2 ∧
      e1*b1 + e2*b2 + e3*b3 = 0))
    (x y : Vec4) :
    minkowskiBilin
      (involutionProjPlus
        (emNormalizedJet
          e1 e2 e3 b1 b2 b3) x)
      (involutionProjMinus
        (emNormalizedJet
          e1 e2 e3 b1 b2 b3) y) = 0 := by
  exact involution_projector_planes_orthogonal
    minkowskiBilin
    (emNormalizedJet
      e1 e2 e3 b1 b2 b3)
    (emNormalizedJet_involution
      e1 e2 e3 b1 b2 b3 hn)
    (emNormalizedJet_selfadjoint
      e1 e2 e3 b1 b2 b3)
    x y

end RelativeRest
