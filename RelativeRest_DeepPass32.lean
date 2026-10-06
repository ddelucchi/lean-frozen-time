import RelativeRest_DeepPass31

/-!
# Relative Rest: deep forced pass 32

Derive the principal electromagnetic energy density from the stress eigenvalue.

If u is unit timelike and the mixed stress endomorphism obeys
  T u = -(chi/(16*pi)) u,
then the observer energy density g(u,T u) is forced to be chi/(16*pi).
Combining chi=omega^2 with positivity therefore gives the manuscript's
  omega^2=16*pi*epsilon_EM,
  omega=4*sqrt(pi*epsilon_EM)
without supplying epsilon_EM=chi/(16*pi) independently.
-/

noncomputable section

open Function Set

namespace RelativeRest

section StressEnergyClock

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- Energy density measured by u from a mixed stress endomorphism. -/
def observerEnergyDensity
    (T : V →ₗ[ℝ] V)
    (u : V) : ℝ :=
  B u (T u)

/-- The principal Maxwell stress eigenvalue forces epsilon_EM=chi/(16*pi). -/
theorem principalStressEigen_forces_energyDensity
    (T : V →ₗ[ℝ] V)
    (u : V)
    (chi : ℝ)
    (hu : B u u = -1)
    (hTu :
      T u =
        (-(chi / (16 * Real.pi))) • u) :
    observerEnergyDensity B T u =
      chi / (16 * Real.pi) := by
  unfold observerEnergyDensity
  rw [hTu, map_smul, hu]
  ring

/-- The stress eigenvalue and chi=omega^2 force the squared clock-energy relation. -/
theorem principalStressEigen_forces_clock_energy
    (T : V →ₗ[ℝ] V)
    (u : V)
    (chi omega : ℝ)
    (hu : B u u = -1)
    (hTu :
      T u =
        (-(chi / (16 * Real.pi))) • u)
    (hchi : chi = omega^2) :
    omega^2 =
      16 * Real.pi * observerEnergyDensity B T u := by
  rw [principalStressEigen_forces_energyDensity
      B T u chi hu hTu,
    hchi]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]

/-- On the positive branch the stress eigenvalue fixes the clock rate itself. -/
theorem principalStressEigen_forces_clock_rate
    (T : V →ₗ[ℝ] V)
    (u : V)
    (chi omega : ℝ)
    (hu : B u u = -1)
    (hTu :
      T u =
        (-(chi / (16 * Real.pi))) • u)
    (hchi : chi = omega^2)
    (hchiNonneg : 0 ≤ chi)
    (homegaNonneg : 0 ≤ omega) :
    omega =
      4 * Real.sqrt
        (Real.pi * observerEnergyDensity B T u) := by
  have hepsilon :
      observerEnergyDensity B T u =
        chi / (16 * Real.pi) :=
    principalStressEigen_forces_energyDensity
      B T u chi hu hTu
  have hepsilonNonneg :
      0 ≤ observerEnergyDensity B T u := by
    rw [hepsilon]
    positivity
  exact clock_rate_eq_four_sqrt_pi_energy
    (observerEnergyDensity B T u)
    omega
    hepsilonNonneg
    homegaNonneg
    (principalStressEigen_forces_clock_energy
      B T u chi omega hu hTu hchi)

end StressEnergyClock

end RelativeRest
