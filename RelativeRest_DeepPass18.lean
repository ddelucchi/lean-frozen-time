import RelativeRest_DeepPass17

/-!
# Relative Rest: deep forced pass 18

Consolidate the invariant clock normalization.

Starting from the carrier magnitude chi, K=chi^2, and the positive square-root clock rate
omega=sqrt(chi), this file proves in one chain the identities used in the manuscript:
  omega^2 = chi,
  K = omega^4,
  omega^2 = 16 pi epsilon_EM,
  omega = 4 sqrt(pi epsilon_EM),
  K = I^2 + J^2
for the principal electromagnetic invariants.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-- The positive clock rate is uniquely the conventional energy-density expression. -/
theorem clock_rate_eq_four_sqrt_pi_energy
    (epsilon omega : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (homega : 0 ≤ omega)
    (hsq : omega^2 = 16 * Real.pi * epsilon) :
    omega = 4 * Real.sqrt (Real.pi * epsilon) := by
  have hpiepsilon : 0 ≤ Real.pi * epsilon :=
    mul_nonneg (le_of_lt Real.pi_pos) hepsilon
  have hsqrt :
      (Real.sqrt (Real.pi * epsilon))^2 =
        Real.pi * epsilon := by
    exact Real.sq_sqrt hpiepsilon
  have hrhs :
      0 ≤ 4 * Real.sqrt (Real.pi * epsilon) := by
    positivity
  nlinarith

/-- Complete principal-frame invariant normalization of the Einstein--Maxwell clock. -/
theorem electromagnetic_clock_full_chain
    (E B chi K omega epsilon : ℝ)
    (hchi : chi = 2 * (E^2 + B^2))
    (hK : K = chi^2)
    (homega : omega = Real.sqrt chi)
    (hepsilon : epsilon = principalEmEnergyDensity E B) :
    omega^2 = chi ∧
    K = omega^4 ∧
    omega^2 = 16 * Real.pi * epsilon ∧
    omega = 4 * Real.sqrt (Real.pi * epsilon) ∧
    K = (maxwellI E B)^2 + (maxwellJ E B)^2 := by
  have hchi_nonneg : 0 ≤ chi := by
    rw [hchi]
    positivity
  have hclock :=
    clock_rate_square K chi omega hchi_nonneg hK homega
  have homega_sq : omega^2 = 2 * (E^2 + B^2) := by
    rw [hclock.1, hchi]
  have henergy :
      omega^2 = 16 * Real.pi * epsilon := by
    rw [hepsilon]
    exact principal_energy_clock_relation E B omega homega_sq
  have hepsilon_nonneg : 0 ≤ epsilon := by
    rw [hepsilon]
    unfold principalEmEnergyDensity
    positivity
  have homega_nonneg : 0 ≤ omega := by
    rw [homega]
    positivity
  have homega_energy :
      omega = 4 * Real.sqrt (Real.pi * epsilon) :=
    clock_rate_eq_four_sqrt_pi_energy
      epsilon omega hepsilon_nonneg homega_nonneg henergy
  have hinvariant :
      omega^4 =
        (maxwellI E B)^2 + (maxwellJ E B)^2 :=
    maxwell_invariant_clock_fourth_power E B omega homega_sq
  exact
    ⟨hclock.1, hclock.2, henergy, homega_energy,
      hclock.2.trans hinvariant⟩

end RelativeRest
