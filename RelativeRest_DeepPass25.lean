import RelativeRest_DeepPass24

/-!
# Relative Rest: deep forced pass 25

Globalize the statement that only the clock origin remains conventional.

Reparametrize the same oriented reference clock line by theta' = theta + C, equivalently
gamma_C(theta') = gamma(theta' - C).  The chronological endpoint sets are then exact translates
of the original endpoint sets.  Conditional completeness of R forces both endpoint values to
translate by the same C.  Consequently radar time shifts by C while radar radius is invariant.

This proves the manuscript's common-origin freedom at the causal-endpoint level, not merely for
two already-chosen endpoint numbers.
-/

noncomputable section

open Function Set

namespace RelativeRest

section CausalOriginShift

variable {X : Type*}

/-- The same oriented clock line after shifting only its parameter origin by C. -/
def shiftedClockLine
    (gamma : ℝ → X) (C : ℝ) : ℝ → X :=
  fun theta => gamma (theta - C)

/-- The chronological past endpoint set is translated by C under an origin shift. -/
theorem pastEndpointSet_shift
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (x : X)
    (C : ℝ) :
    pastEndpointSet Chrono (shiftedClockLine gamma C) x =
      (fun theta : ℝ => theta + C) ''
        pastEndpointSet Chrono gamma x := by
  ext theta
  constructor
  · intro h
    refine ⟨theta - C, ?_, ?_⟩
    · exact h
    · ring
  · rintro ⟨eta, heta, rfl⟩
    simpa [shiftedClockLine] using heta

/-- The chronological future endpoint set is translated by the same C. -/
theorem futureEndpointSet_shift
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (x : X)
    (C : ℝ) :
    futureEndpointSet Chrono (shiftedClockLine gamma C) x =
      (fun theta : ℝ => theta + C) ''
        futureEndpointSet Chrono gamma x := by
  ext theta
  constructor
  · intro h
    refine ⟨theta - C, ?_, ?_⟩
    · exact h
    · ring
  · rintro ⟨eta, heta, rfl⟩
    simpa [shiftedClockLine] using heta

/-- The finite past endpoint value shifts by exactly C. -/
theorem causalThetaMinus_shift
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (x : X)
    (C : ℝ)
    (hne : (pastEndpointSet Chrono gamma x).Nonempty)
    (hbdd : BddAbove (pastEndpointSet Chrono gamma x)) :
    causalThetaMinus Chrono (shiftedClockLine gamma C) x =
      causalThetaMinus Chrono gamma x + C := by
  unfold causalThetaMinus
  rw [pastEndpointSet_shift Chrono gamma x C]
  exact ((OrderIso.addRight C).map_csSup' hne hbdd).symm

/-- The finite future endpoint value shifts by exactly C. -/
theorem causalThetaPlus_shift
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (x : X)
    (C : ℝ)
    (hne : (futureEndpointSet Chrono gamma x).Nonempty)
    (hbdd : BddBelow (futureEndpointSet Chrono gamma x)) :
    causalThetaPlus Chrono (shiftedClockLine gamma C) x =
      causalThetaPlus Chrono gamma x + C := by
  unfold causalThetaPlus
  rw [futureEndpointSet_shift Chrono gamma x C]
  exact ((OrderIso.addRight C).map_csInf' hne hbdd).symm

/-- A common clock-origin change translates radar time and leaves radar radius invariant. -/
theorem causalRadar_origin_shift
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (x : X)
    (C : ℝ)
    (hpastNe : (pastEndpointSet Chrono gamma x).Nonempty)
    (hpastBdd : BddAbove (pastEndpointSet Chrono gamma x))
    (hfutureNe : (futureEndpointSet Chrono gamma x).Nonempty)
    (hfutureBdd : BddBelow (futureEndpointSet Chrono gamma x)) :
    causalRadarTime Chrono (shiftedClockLine gamma C) x =
        causalRadarTime Chrono gamma x + C ∧
    causalRadarRadius Chrono (shiftedClockLine gamma C) x =
        causalRadarRadius Chrono gamma x := by
  have hminus :=
    causalThetaMinus_shift
      Chrono gamma x C hpastNe hpastBdd
  have hplus :=
    causalThetaPlus_shift
      Chrono gamma x C hfutureNe hfutureBdd
  unfold causalRadarTime causalRadarRadius
  rw [hminus, hplus]
  exact radar_common_shift
    (causalThetaPlus Chrono gamma x)
    (causalThetaMinus Chrono gamma x)
    C

end CausalOriginShift

end RelativeRest
