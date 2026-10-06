import RelativeRest_DeepPass36

/-!
# Relative Rest: deep forced pass 37

Strengthen the relational observable from a translated derivative formula to a complete observable.

Assume the characteristic flow is an additive R-action and the intrinsic clock advances covariantly,
  T(flow_s x)=T(x)+s.
Then
  O_F(theta;x)=F(flow_{theta-T(x)} x)
is invariant under moving x anywhere along the same characteristic/gauge orbit.  At theta=T(x)
it reduces to F(x), and a simultaneous additive shift of T and theta changes nothing.

Together with the existing derivative theorem, this is the precise algebraic content of converting
the frozen characteristic flow into relational evolution.
-/

noncomputable section

open Function Set

namespace RelativeRest

section CompleteObservable

variable {X : Type*}

/-- Simultaneous shift of the clock origin and relational label leaves the observable unchanged. -/
theorem relationalObservable_origin_invariant
    (flow : ℝ → X → X)
    (F : X → ℝ)
    (T : X → ℝ)
    (C theta : ℝ)
    (x : X) :
    relationalObservable flow F
        (fun y => T y + C)
        (theta + C) x =
      relationalObservable flow F T theta x := by
  unfold relationalObservable
  congr 2
  ring

/-- At the intrinsic clock reading of x, the relational observable reduces to F(x). -/
theorem relationalObservable_at_clock
    (flow : ℝ → X → X)
    (F : X → ℝ)
    (T : X → ℝ)
    (hzero : ∀ x : X, flow 0 x = x)
    (x : X) :
    relationalObservable flow F T (T x) x = F x := by
  unfold relationalObservable
  rw [sub_self, hzero]

/-- If the clock advances by the flow parameter, the complete observable is constant along each
characteristic/gauge orbit. -/
theorem relationalObservable_gauge_invariant
    (flow : ℝ → X → X)
    (F : X → ℝ)
    (T : X → ℝ)
    (hadd : ∀ a b : ℝ, ∀ x : X,
      flow a (flow b x) = flow (a + b) x)
    (hclock : ∀ s : ℝ, ∀ x : X,
      T (flow s x) = T x + s)
    (theta s : ℝ)
    (x : X) :
    relationalObservable flow F T theta (flow s x) =
      relationalObservable flow F T theta x := by
  unfold relationalObservable
  rw [hclock s x, hadd]
  congr 2
  ring

/-- Full relational-evolution certificate: gauge-orbit invariance, recovery of the original
observable at the intrinsic clock reading, and the X_* evolution equation. -/
theorem relational_complete_observable_certificate
    (flow : ℝ → X → X)
    (F XF : X → ℝ)
    (T : X → ℝ)
    (hzero : ∀ x : X, flow 0 x = x)
    (hadd : ∀ a b : ℝ, ∀ x : X,
      flow a (flow b x) = flow (a + b) x)
    (hclock : ∀ s : ℝ, ∀ x : X,
      T (flow s x) = T x + s)
    (hgenerator : ∀ t : ℝ, ∀ x : X,
      HasDerivAt
        (fun s => F (flow s x))
        (XF (flow t x)) t)
    (theta s : ℝ)
    (x : X) :
    relationalObservable flow F T theta (flow s x) =
        relationalObservable flow F T theta x ∧
    relationalObservable flow F T (T x) x = F x ∧
    deriv
        (fun vartheta =>
          relationalObservable flow F T vartheta x)
        theta =
      XF (flow (theta - T x) x) := by
  exact
    ⟨relationalObservable_gauge_invariant
        flow F T hadd hclock theta s x,
      relationalObservable_at_clock
        flow F T hzero x,
      relationalObservable_deriv
        flow F XF T theta x
        (fun t => hgenerator t x)⟩

end CompleteObservable

end RelativeRest
