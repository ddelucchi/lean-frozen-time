import RelativeRest_DeepPass7

/-!
# Relative Rest: deep forced pass 8

Abstract causal-endpoint globalization.

The manuscript's global clock values are defined from chronological endpoint sets, not by choosing
a null geodesic branch.  This file formalizes the order-theoretic core: transitivity/push-up gives
set inclusion, endpoint suprema/infima are monotone, the past endpoint precedes the future endpoint
under the causal separation condition, and the radar midpoint inherits monotonicity.
-/

noncomputable section

open Function Set

namespace RelativeRest

section CausalEndpoints

variable {X : Type*}

/-- Parameters on the reference clock line chronologically before the event x. -/
def pastEndpointSet
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (x : X) : Set ℝ :=
  {theta | Chrono (gamma theta) x}

/-- Parameters on the reference clock line chronologically after the event x. -/
def futureEndpointSet
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (x : X) : Set ℝ :=
  {theta | Chrono x (gamma theta)}

/-- Finite lower endpoint used on the domain where the past endpoint set is nonempty and bounded. -/
def causalThetaMinus
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (x : X) : ℝ :=
  sSup (pastEndpointSet Chrono gamma x)

/-- Finite upper endpoint used on the domain where the future endpoint set is nonempty and bounded. -/
def causalThetaPlus
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (x : X) : ℝ :=
  sInf (futureEndpointSet Chrono gamma x)

def causalRadarTime
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (x : X) : ℝ :=
  radarTime
    (causalThetaPlus Chrono gamma x)
    (causalThetaMinus Chrono gamma x)

def causalRadarRadius
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (x : X) : ℝ :=
  radarRadius
    (causalThetaPlus Chrono gamma x)
    (causalThetaMinus Chrono gamma x)

/-- Push-up/transitivity enlarges the chronological-past endpoint set. -/
theorem pastEndpointSet_mono
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (htrans : ∀ a b c : X, Chrono a b → Chrono b c → Chrono a c)
    {x y : X}
    (hxy : Chrono x y) :
    pastEndpointSet Chrono gamma x ⊆
      pastEndpointSet Chrono gamma y := by
  intro theta htheta
  exact htrans (gamma theta) x y htheta hxy

/-- Push-up/transitivity shrinks the chronological-future endpoint set. -/
theorem futureEndpointSet_antitone
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (htrans : ∀ a b c : X, Chrono a b → Chrono b c → Chrono a c)
    {x y : X}
    (hxy : Chrono x y) :
    futureEndpointSet Chrono gamma y ⊆
      futureEndpointSet Chrono gamma x := by
  intro theta htheta
  exact htrans x y (gamma theta) hxy htheta

/-- The lower causal endpoint is monotone along chronological order. -/
theorem causalThetaMinus_mono
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (htrans : ∀ a b c : X, Chrono a b → Chrono b c → Chrono a c)
    {x y : X}
    (hxy : Chrono x y)
    (hyBdd : BddAbove (pastEndpointSet Chrono gamma y))
    (hxNonempty : (pastEndpointSet Chrono gamma x).Nonempty) :
    causalThetaMinus Chrono gamma x ≤
      causalThetaMinus Chrono gamma y := by
  unfold causalThetaMinus
  exact csSup_le_csSup hyBdd hxNonempty
    (pastEndpointSet_mono Chrono gamma htrans hxy)

/-- The upper causal endpoint is monotone along chronological order. -/
theorem causalThetaPlus_mono
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (htrans : ∀ a b c : X, Chrono a b → Chrono b c → Chrono a c)
    {x y : X}
    (hxy : Chrono x y)
    (hxBdd : BddBelow (futureEndpointSet Chrono gamma x))
    (hyNonempty : (futureEndpointSet Chrono gamma y).Nonempty) :
    causalThetaPlus Chrono gamma x ≤
      causalThetaPlus Chrono gamma y := by
  unfold causalThetaPlus
  exact csInf_le_csInf hxBdd hyNonempty
    (futureEndpointSet_antitone Chrono gamma htrans hxy)

/-- If every past endpoint parameter precedes every future endpoint parameter, the two finite
causal endpoints occur in the correct order. -/
theorem causalThetaMinus_le_ThetaPlus
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (x : X)
    (hpast : (pastEndpointSet Chrono gamma x).Nonempty)
    (hfuture : (futureEndpointSet Chrono gamma x).Nonempty)
    (hseparate :
      ∀ thetaMinus ∈ pastEndpointSet Chrono gamma x,
      ∀ thetaPlus ∈ futureEndpointSet Chrono gamma x,
        thetaMinus ≤ thetaPlus) :
    causalThetaMinus Chrono gamma x ≤
      causalThetaPlus Chrono gamma x := by
  unfold causalThetaMinus causalThetaPlus
  apply csSup_le hpast
  intro thetaMinus hminus
  apply le_csInf hfuture
  intro thetaPlus hplus
  exact hseparate thetaMinus hminus thetaPlus hplus

/-- Once both endpoint values are monotone, their exchange-even midpoint is monotone. -/
theorem causalRadarTime_mono_of_endpoints
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    {x y : X}
    (hminus :
      causalThetaMinus Chrono gamma x ≤
        causalThetaMinus Chrono gamma y)
    (hplus :
      causalThetaPlus Chrono gamma x ≤
        causalThetaPlus Chrono gamma y) :
    causalRadarTime Chrono gamma x ≤
      causalRadarTime Chrono gamma y := by
  unfold causalRadarTime radarTime
  linarith

/-- Full monotonicity certificate from transitivity and the finite-endpoint hypotheses. -/
theorem causalRadarTime_mono
    (Chrono : X → X → Prop)
    (gamma : ℝ → X)
    (htrans : ∀ a b c : X, Chrono a b → Chrono b c → Chrono a c)
    {x y : X}
    (hxy : Chrono x y)
    (hyPastBdd : BddAbove (pastEndpointSet Chrono gamma y))
    (hxPastNonempty : (pastEndpointSet Chrono gamma x).Nonempty)
    (hxFutureBdd : BddBelow (futureEndpointSet Chrono gamma x))
    (hyFutureNonempty : (futureEndpointSet Chrono gamma y).Nonempty) :
    causalRadarTime Chrono gamma x ≤
      causalRadarTime Chrono gamma y := by
  apply causalRadarTime_mono_of_endpoints
  · exact causalThetaMinus_mono Chrono gamma htrans hxy
      hyPastBdd hxPastNonempty
  · exact causalThetaPlus_mono Chrono gamma htrans hxy
      hxFutureBdd hyFutureNonempty

/-- The endpoint construction is intrinsically branch-free at the level of its data: equality of
the chronological relation and reference clock line forces equality of both endpoints. -/
theorem causal_endpoints_ext
    (Chrono1 Chrono2 : X → X → Prop)
    (gamma1 gamma2 : ℝ → X)
    (hChrono : Chrono1 = Chrono2)
    (hgamma : gamma1 = gamma2)
    (x : X) :
    causalThetaMinus Chrono1 gamma1 x =
      causalThetaMinus Chrono2 gamma2 x ∧
    causalThetaPlus Chrono1 gamma1 x =
      causalThetaPlus Chrono2 gamma2 x := by
  subst Chrono2
  subst gamma2
  exact ⟨rfl, rfl⟩

end CausalEndpoints

end RelativeRest
