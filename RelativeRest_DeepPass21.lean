import RelativeRest_DeepPass20

/-!
# Relative Rest: deep forced pass 21

Close the orthogonality part of the Rainich principal-plane split.

For a self-adjoint involution S, vectors in the +1 and -1 eigenspaces are orthogonal.  Therefore
the projectors P_+=(I+S)/2 and P_-=(I-S)/2 produced by the carrier do not merely split the vector
space algebraically: their images are orthogonal for the background symmetric bilinear form.
The result is then instantiated for the normalized Rainich carrier S=chi^{-1} J.
-/

noncomputable section

open Function Set

namespace RelativeRest

section SelfAdjointInvolution

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- Opposite eigenspaces of a self-adjoint involution are orthogonal. -/
theorem opposite_eigenvectors_orthogonal
    (S : V →ₗ[ℝ] V)
    (hself : ∀ x y : V, B x (S y) = B (S x) y)
    (x y : V)
    (hx : S x = x)
    (hy : S y = -y) :
    B x y = 0 := by
  have h := hself x y
  rw [hx, hy] at h
  simp at h
  linarith

/-- Hence the canonical involution projectors have mutually orthogonal images. -/
theorem involution_projector_planes_orthogonal
    (S : V →ₗ[ℝ] V)
    (hS : S.comp S = LinearMap.id)
    (hself : ∀ x y : V, B x (S y) = B (S x) y)
    (x y : V) :
    B (involutionProjPlus S x)
      (involutionProjMinus S y) = 0 := by
  exact opposite_eigenvectors_orthogonal
    B S hself
    (involutionProjPlus S x)
    (involutionProjMinus S y)
    (involution_plus_eigen S hS x)
    (involution_minus_eigen S hS y)

/-- Scalar normalization preserves self-adjointness of the carrier. -/
theorem normalizedCarrier_selfadjoint
    (J : V →ₗ[ℝ] V)
    (chi : ℝ)
    (hself : ∀ x y : V, B x (J y) = B (J x) y) :
    ∀ x y : V,
      B x (((chi⁻¹) • J) y) =
        B (((chi⁻¹) • J) x) y := by
  intro x y
  simp [hself x y]

/-- A nondegenerate Rainich carrier therefore forces an orthogonal principal-plane split. -/
theorem rainich_principal_planes_orthogonal
    (J : V →ₗ[ℝ] V)
    (chi : ℝ)
    (hchi : chi ≠ 0)
    (hRainich :
      J.comp J = (chi^2) • LinearMap.id)
    (hself : ∀ x y : V, B x (J y) = B (J x) y)
    (x y : V) :
    B
      (involutionProjPlus ((chi⁻¹) • J) x)
      (involutionProjMinus ((chi⁻¹) • J) y) = 0 := by
  have hS :
      (((chi⁻¹) • J).comp ((chi⁻¹) • J)) =
        LinearMap.id :=
    normalized_involution J chi hchi hRainich
  exact involution_projector_planes_orthogonal
    B ((chi⁻¹) • J) hS
    (normalizedCarrier_selfadjoint B J chi hself)
    x y

end SelfAdjointInvolution

end RelativeRest
