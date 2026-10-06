import RelativeRest_DeepPass4

/-!
# Relative Rest: deep forced pass 5

This layer formalizes three further end-matter claims:
* the coefficient forced by the self-adjoint carrier decomposition,
* the exact homogeneous algebra of the (Theta,kappa) clock cover,
* and the descending jet-stabilizer logic.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-! ## A. Self-adjoint carrier forces the local clock coefficient -/

section CarrierCoefficient

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- Abstract local version of the manuscript's decomposition
J v = a(v) u + w with w orthogonal to u. -/
theorem selfadjoint_carrier_forces_clock_coefficient
    (J : V →ₗ[ℝ] V)
    (u w v : V)
    (chi omega a : ℝ)
    (T : V →ₗ[ℝ] ℝ)
    (hsym : ∀ x y : V, B x y = B y x)
    (hself : ∀ x y : V, B x (J y) = B (J x) y)
    (hu : B u u = -1)
    (hJu : J u = chi • u)
    (hchi : chi = omega^2)
    (hT : ∀ x : V, T x = -omega * B u x)
    (hw : B u w = 0)
    (hdecomp : J v = a • u + w) :
    a = omega * T v := by
  have hleft : B u (J v) = -a := by
    rw [hdecomp]
    simp only [map_add, map_smul]
    rw [hu, hw]
    ring
  have hright : B u (J v) = chi * B u v := by
    rw [hself u v, hJu]
    simp
  calc
    a = -(B u (J v)) := by linarith
    _ = -(chi * B u v) := by rw [hright]
    _ = omega * T v := by
      rw [hchi, hT v]
      ring

/-- For positive/nonzero clock rate, the optical covector and spatial orthogonality have the same
kernel. -/
theorem optical_covector_kernel_iff_orthogonal
    (u v : V)
    (omega : ℝ)
    (T : V →ₗ[ℝ] ℝ)
    (homega : omega ≠ 0)
    (hT : ∀ x : V, T x = -omega * B u x) :
    T v = 0 ↔ B u v = 0 := by
  rw [hT v]
  constructor
  · intro h
    have hcoef : -omega ≠ 0 := neg_ne_zero.mpr homega
    exact (mul_eq_zero.mp h).resolve_left hcoef
  · intro h
    rw [h]
    ring

end CarrierCoefficient

/-! ## B. Exact homogeneous clock-cover algebra -/

/-- The homogeneous clock-cover one-form at the point (Theta,kappa). -/
def clockThetaForm (p v : R2) : ℝ :=
  p.2 * v.1

/-- The positive-scale Euler/dilation vector kappa partial_kappa. -/
def clockDilation (p : R2) : R2 :=
  (0, p.2)

/-- Common-scale action on the clock cover. -/
def clockScale (c : ℝ) (p : R2) : R2 :=
  (p.1, c * p.2)

/-- Tangent map of common scaling. -/
def clockScaleTangent (c : ℝ) (v : R2) : R2 :=
  (v.1, c * v.2)

/-- Contraction of the canonical two-form with the Euler field is exactly kappa dTheta. -/
theorem clockOmega_contract_dilation
    (p v : R2) :
    clockOmega (clockDilation p) v = clockThetaForm p v := by
  rcases p with ⟨theta, kappa⟩
  rcases v with ⟨dtheta, dkappa⟩
  norm_num [clockOmega, clockDilation, clockThetaForm]

/-- The clock one-form is one-homogeneous under positive/common scaling; algebraically positivity
is not needed for the equality itself. -/
theorem clockThetaForm_scale
    (c : ℝ) (p v : R2) :
    clockThetaForm (clockScale c p) (clockScaleTangent c v) =
      c * clockThetaForm p v := by
  rcases p with ⟨theta, kappa⟩
  rcases v with ⟨dtheta, dkappa⟩
  simp [clockThetaForm, clockScale, clockScaleTangent]
  ring

/-- The canonical two-form has the same weight-one homogeneity. -/
theorem clockOmega_scale
    (c : ℝ) (v w : R2) :
    clockOmega (clockScaleTangent c v) (clockScaleTangent c w) =
      c * clockOmega v w := by
  rcases v with ⟨vtheta, vkappa⟩
  rcases w with ⟨wtheta, wkappa⟩
  simp [clockOmega, clockScaleTangent]
  ring

/-- The coordinate pair is canonical with the manuscript's sign convention. -/
theorem clock_cover_canonical_pair :
    clockOmega dKappaVec dThetaVec = 1 := by
  exact clockOmega_coordinates.1

/-! ## C. Descending stabilizers of the fixed-point jet -/

section JetStabilizer

variable {G : Type*}

/-- Exact residual stabilizer of the full formal jet. -/
def infiniteJetStabilizer (H : ℕ → Set G) : Set G :=
  ⋂ m, H m

theorem mem_infiniteJetStabilizer_iff
    (H : ℕ → Set G) (g : G) :
    g ∈ infiniteJetStabilizer H ↔ ∀ m, g ∈ H m := by
  simp [infiniteJetStabilizer]

/-- Any finite jet with trivial stabilizer forces the full-jet stabilizer to be trivial, provided
the identity element belongs to every stabilizer. -/
theorem finite_trivial_stabilizer_forces_full_trivial
    (H : ℕ → Set G)
    (e : G)
    (he : ∀ m, e ∈ H m)
    (m : ℕ)
    (hm : H m = {e}) :
    infiniteJetStabilizer H = {e} := by
  ext g
  constructor
  · intro hg
    have hgm : g ∈ H m :=
      (mem_infiniteJetStabilizer_iff H g).mp hg m
    rw [hm] at hgm
    simpa using hgm
  · intro hg
    have hge : g = e := by simpa using hg
    subst g
    exact (mem_infiniteJetStabilizer_iff H e).mpr he

/-- If higher jets only reduce stabilizers, the full residual isotropy is contained in every
finite-order stabilizer. -/
theorem infinite_stabilizer_subset_finite
    (H : ℕ → Set G)
    (m : ℕ) :
    infiniteJetStabilizer H ⊆ H m := by
  intro g hg
  exact (mem_infiniteJetStabilizer_iff H g).mp hg m

end JetStabilizer

end RelativeRest
