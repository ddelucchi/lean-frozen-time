import Mathlib

/-!
# Maxwell action: a first-principles finite-jet variational layer

This file works directly with the local four-dimensional Maxwell potential first jet
  D_mu A_nu
in a fixed orthonormal Lorentz frame. It constructs the antisymmetric field strength,
proves invariance under addition of a symmetric gauge Hessian, and checks the local
quadratic action. A separate general theorem gives the **exact**, rather than merely
infinitesimal, first- and second-order increments of a quadratic Lagrangian.

This is a genuine step backward toward the Einstein--Maxwell action. It is NOT a
formalization of the metric variation, the Levi-Civita connection, the spacetime
integration-by-parts formula, the Einstein equations, or the Iyer--Wald identity.
Those cannot be inferred from the finite-jet results below.
-/

noncomputable section

open scoped BigOperators

namespace RelativeRest
namespace MaxwellAction

/-- At one spacetime point in an orthonormal frame, D_mu A_nu is a first jet. -/
abbrev PotentialJet := Fin 4 → Fin 4 → ℝ

/-- The Maxwell two-form from a potential first jet, F_mu_nu = D_mu A_nu - D_nu A_mu. -/
def fieldStrength (D : PotentialJet) : PotentialJet :=
  fun mu nu => D mu nu - D nu mu

theorem fieldStrength_antisymmetric
    (D : PotentialJet) (mu nu : Fin 4) :
    fieldStrength D mu nu = -fieldStrength D nu mu := by
  dsimp [fieldStrength]
  ring

theorem fieldStrength_diagonal_zero
    (D : PotentialJet) (mu : Fin 4) :
    fieldStrength D mu mu = 0 := by
  simp [fieldStrength]

/-- The exterior derivative is linear already at the first-jet level. -/
theorem fieldStrength_add_scaled
    (D H : PotentialJet) (t : ℝ) :
    fieldStrength (fun mu nu => D mu nu + t * H mu nu) =
      fun mu nu => fieldStrength D mu nu + t * fieldStrength H mu nu := by
  funext mu nu
  dsimp [fieldStrength]
  ring

/-- A gauge-potential shift changes the first jet by a symmetric Hessian.
    Therefore F=dA is unchanged, without assuming Maxwell's field equations. -/
theorem fieldStrength_gauge_invariant
    (D H : PotentialJet)
    (hH : ∀ mu nu : Fin 4, H mu nu = H nu mu) :
    fieldStrength (fun mu nu => D mu nu + H mu nu) =
      fieldStrength D := by
  funext mu nu
  dsimp [fieldStrength]
  rw [hH nu mu]
  ring

/-- Signature (-,+,+,+), in the same orthonormal-frame convention as the
    fixed-point Maxwell stress calculation. -/
def lorentzSign (mu : Fin 4) : ℝ :=
  if mu = 0 then -1 else 1

/-- F_mu_nu G^mu_nu, with the metric factors written explicitly. -/
def contraction (F G : PotentialJet) : ℝ :=
  ∑ mu : Fin 4, ∑ nu : Fin 4,
    lorentzSign mu * lorentzSign nu * F mu nu * G mu nu

theorem contraction_symmetric (F G : PotentialJet) :
    contraction F G = contraction G F := by
  unfold contraction
  apply Finset.sum_congr rfl
  intro mu hmu
  apply Finset.sum_congr rfl
  intro nu hnu
  ring

/-- The conventional flat-frame Maxwell kinetic density, -1/4 F_ab F^ab. -/
def density (D : PotentialJet) : ℝ :=
  -(1 / 4 : ℝ) *
    contraction (fieldStrength D) (fieldStrength D)

/-- Local U(1) gauge invariance of the kinetic density, proved from d^2 lambda=0
    (symmetry of the Hessian). No gauge-invariance axiom is postulated. -/
theorem density_gauge_invariant
    (D H : PotentialJet)
    (hH : ∀ mu nu : Fin 4, H mu nu = H nu mu) :
    density (fun mu nu => D mu nu + H mu nu) = density D := by
  unfold density
  rw [fieldStrength_gauge_invariant D H hH]

/-- Gauge invariance holds along an entire affine gauge orbit. -/
theorem density_gauge_orbit_constant
    (D H : PotentialJet)
    (hH : ∀ mu nu : Fin 4, H mu nu = H nu mu)
    (t : ℝ) :
    density (fun mu nu => D mu nu + t * H mu nu) = density D := by
  apply density_gauge_invariant
  intro mu nu
  exact congrArg (fun x : ℝ => t * x) (hH mu nu)

section QuadraticVariation

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The quadratic kinetic Lagrangian with a bilinear constitutive contraction.
    For the electromagnetic field this contraction is metric-dependent; here it
    is treated as an explicitly supplied bilinear map. -/
def quadraticDensity
    (C : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : V) : ℝ :=
  -(1 / 4 : ℝ) * C F F

/-- Exact finite variation, including the second-order remainder. This uses only
    bilinearity and does NOT assume symmetry of the contraction. -/
theorem quadraticDensity_exact_increment
    (C : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (F H : V) (t : ℝ) :
    quadraticDensity C (F + t • H) - quadraticDensity C F =
      -(t / 4) * (C F H + C H F) -
        (t ^ 2 / 4) * C H H := by
  simp only [quadraticDensity, map_add, map_smul, smul_eq_mul]
  ring

/-- With the symmetric Maxwell contraction, the linear response is forced to be
    -1/2 C(F,H), and the quadratic remainder is explicit. This is the local
    algebraic precursor of the Maxwell Euler--Lagrange variation. -/
theorem quadraticDensity_symmetric_increment
    (C : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hC : ∀ X Y : V, C X Y = C Y X)
    (F H : V) (t : ℝ) :
    quadraticDensity C (F + t • H) - quadraticDensity C F =
      -(t / 2) * C F H -
        (t ^ 2 / 4) * C H H := by
  calc
    quadraticDensity C (F + t • H) - quadraticDensity C F =
        -(t / 4) * (C F H + C H F) -
          (t ^ 2 / 4) * C H H :=
      quadraticDensity_exact_increment C F H t
    _ = -(t / 2) * C F H -
          (t ^ 2 / 4) * C H H := by
      rw [hC H F]
      ring

end QuadraticVariation
end MaxwellAction
end RelativeRest
