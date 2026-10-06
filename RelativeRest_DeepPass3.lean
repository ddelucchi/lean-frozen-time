import RelativeRest_DeepPass2

/-!
# Relative Rest: deep forced pass 3

This layer closes additional algebraic steps that appear explicitly in the manuscript:
Rainich eigenspace projectors, common-scale invariance of the logarithmic carrier,
exchange-forced radar time/radius, origin-shift freedom, the principal Maxwell clock invariant,
and relational evolution along a translated flow parameter.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-! ## A. Rainich involution projectors -/

section InvolutionProjectors

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def involutionProjPlus (S : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id + S)

def involutionProjMinus (S : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id - S)

theorem involution_projectors_sum
    (S : V →ₗ[ℝ] V) (v : V) :
    involutionProjPlus S v + involutionProjMinus S v = v := by
  simp [involutionProjPlus, involutionProjMinus]
  module

theorem involution_projectors_difference
    (S : V →ₗ[ℝ] V) (v : V) :
    involutionProjPlus S v - involutionProjMinus S v = S v := by
  simp [involutionProjPlus, involutionProjMinus]
  module

theorem involution_plus_eigen
    (S : V →ₗ[ℝ] V)
    (hS : S.comp S = LinearMap.id)
    (v : V) :
    S (involutionProjPlus S v) = involutionProjPlus S v := by
  have hpoint : S (S v) = v := by
    have h := LinearMap.congr_fun hS v
    simpa using h
  simp [involutionProjPlus, map_smul, map_add, hpoint]
  module

theorem involution_minus_eigen
    (S : V →ₗ[ℝ] V)
    (hS : S.comp S = LinearMap.id)
    (v : V) :
    S (involutionProjMinus S v) = - involutionProjMinus S v := by
  have hpoint : S (S v) = v := by
    have h := LinearMap.congr_fun hS v
    simpa using h
  simp [involutionProjMinus, map_smul, map_sub, hpoint]
  module

theorem involution_plus_idempotent
    (S : V →ₗ[ℝ] V)
    (hS : S.comp S = LinearMap.id)
    (v : V) :
    involutionProjPlus S (involutionProjPlus S v) =
      involutionProjPlus S v := by
  simp [involutionProjPlus, involution_plus_eigen S hS]
  module

theorem involution_minus_idempotent
    (S : V →ₗ[ℝ] V)
    (hS : S.comp S = LinearMap.id)
    (v : V) :
    involutionProjMinus S (involutionProjMinus S v) =
      involutionProjMinus S v := by
  simp [involutionProjMinus, involution_minus_eigen S hS]
  module

theorem involution_cross_plus_minus_zero
    (S : V →ₗ[ℝ] V)
    (hS : S.comp S = LinearMap.id)
    (v : V) :
    involutionProjPlus S (involutionProjMinus S v) = 0 := by
  simp [involutionProjPlus, involution_minus_eigen S hS]
  module

theorem involution_cross_minus_plus_zero
    (S : V →ₗ[ℝ] V)
    (hS : S.comp S = LinearMap.id)
    (v : V) :
    involutionProjMinus S (involutionProjPlus S v) = 0 := by
  simp [involutionProjMinus, involution_plus_eigen S hS]
  module

end InvolutionProjectors

/-! ## B. Common-scale invariance of the logarithmic carrier -/

theorem log_constant_scale_hasDerivAt
    (f : ℝ → ℝ) (c x f' : ℝ)
    (hc : c ≠ 0)
    (hfx : f x ≠ 0)
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => Real.log (c * f y)) (f' / f x) x := by
  have hscaled := hf.const_mul c
  have hscaled0 : c * f x ≠ 0 := mul_ne_zero hc hfx
  have hlog := hscaled.log hscaled0
  convert hlog using 1
  field_simp [hc, hfx]
  ring

/-- The logarithmic derivative itself is unchanged by a nonzero constant scale. -/
theorem log_constant_scale_deriv
    (f : ℝ → ℝ) (c x f' : ℝ)
    (hc : c ≠ 0)
    (hfx : f x ≠ 0)
    (hf : HasDerivAt f f' x) :
    deriv (fun y => Real.log (c * f y)) x = f' / f x :=
  (log_constant_scale_hasDerivAt f c x f' hc hfx hf).deriv

/-! ## C. Exchange-forced radar decomposition -/

def radarTime (thetaPlus thetaMinus : ℝ) : ℝ :=
  (thetaPlus + thetaMinus) / 2

def radarRadius (thetaPlus thetaMinus : ℝ) : ℝ :=
  (thetaPlus - thetaMinus) / 2

theorem radar_reconstruct_plus (thetaPlus thetaMinus : ℝ) :
    radarTime thetaPlus thetaMinus + radarRadius thetaPlus thetaMinus =
      thetaPlus := by
  unfold radarTime radarRadius
  ring

theorem radar_reconstruct_minus (thetaPlus thetaMinus : ℝ) :
    radarTime thetaPlus thetaMinus - radarRadius thetaPlus thetaMinus =
      thetaMinus := by
  unfold radarTime radarRadius
  ring

theorem radar_exchange_even (thetaPlus thetaMinus : ℝ) :
    radarTime thetaMinus thetaPlus = radarTime thetaPlus thetaMinus := by
  unfold radarTime
  ring

theorem radar_exchange_odd (thetaPlus thetaMinus : ℝ) :
    radarRadius thetaMinus thetaPlus = - radarRadius thetaPlus thetaMinus := by
  unfold radarRadius
  ring

/-- The even/odd midpoint-radius pair is uniquely forced by the two null endpoint values. -/
theorem radar_decomposition_unique
    (thetaPlus thetaMinus T R : ℝ)
    (hplus : thetaPlus = T + R)
    (hminus : thetaMinus = T - R) :
    T = radarTime thetaPlus thetaMinus ∧
      R = radarRadius thetaPlus thetaMinus := by
  constructor
  · unfold radarTime
    linarith
  · unfold radarRadius
    linarith

/-- A common endpoint shift changes only the clock origin. -/
theorem radar_common_shift
    (thetaPlus thetaMinus C : ℝ) :
    radarTime (thetaPlus + C) (thetaMinus + C) =
        radarTime thetaPlus thetaMinus + C ∧
    radarRadius (thetaPlus + C) (thetaMinus + C) =
        radarRadius thetaPlus thetaMinus := by
  constructor <;> unfold radarTime radarRadius <;> ring

/-! ## D. Principal Maxwell invariant and clock rate -/

/-- Principal-frame electromagnetic energy density in Gaussian units. -/
def principalEmEnergyDensity (E B : ℝ) : ℝ :=
  (E^2 + B^2) / (8 * Real.pi)

theorem principal_energy_density_relation
    (E B : ℝ) :
    16 * Real.pi * principalEmEnergyDensity E B =
      2 * (E^2 + B^2) := by
  unfold principalEmEnergyDensity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

/-- If the squared clock rate is the carrier magnitude 2(E^2+B^2), its fourth power is exactly
the invariant Maxwell combination I^2+J^2. -/
theorem maxwell_invariant_clock_fourth_power
    (E B omega : ℝ)
    (homega : omega^2 = 2 * (E^2 + B^2)) :
    omega^4 = (maxwellI E B)^2 + (maxwellJ E B)^2 := by
  rw [maxwell_invariant_square]
  calc
    omega^4 = (omega^2)^2 := by ring
    _ = (2 * (E^2 + B^2))^2 := by rw [homega]
    _ = 4 * (E^2 + B^2)^2 := by ring

theorem principal_energy_clock_relation
    (E B omega : ℝ)
    (homega : omega^2 = 2 * (E^2 + B^2)) :
    omega^2 = 16 * Real.pi * principalEmEnergyDensity E B := by
  rw [principal_energy_density_relation]
  exact homega

/-! ## E. Local integrability/Frobenius scalar content -/

theorem spatial_clock_curvature_zero_iff
    (omega varpi : ℝ) (homega : omega ≠ 0) :
    -2 * omega * varpi = 0 ↔ varpi = 0 := by
  constructor
  · intro h
    have hcoef : -2 * omega ≠ 0 := mul_ne_zero (by norm_num) homega
    exact (mul_eq_zero.mp h).resolve_left hcoef
  · rintro rfl
    ring

/-! ## F. Relational observable along an actual flow parameter -/

section RelationalFlow

variable {X : Type*}

def relationalObservable
    (flow : ℝ → X → X)
    (F : X → ℝ)
    (T : X → ℝ)
    (theta : ℝ)
    (x : X) : ℝ :=
  F (flow (theta - T x) x)

/-- Translation by the intrinsic clock does not change the flow derivative. -/
theorem relationalObservable_hasDerivAt
    (flow : ℝ → X → X)
    (F : X → ℝ)
    (T : X → ℝ)
    (theta v : ℝ)
    (x : X)
    (hflow : HasDerivAt (fun t => F (flow t x)) v (theta - T x)) :
    HasDerivAt
      (fun vartheta => relationalObservable flow F T vartheta x)
      v theta := by
  unfold relationalObservable
  simpa using hflow.comp_sub_const theta (T x)

/-- If the orbit derivative is the generator XF at every flow time, the relational observable
obeys exactly the manuscript's evolution equation. -/
theorem relationalObservable_deriv
    (flow : ℝ → X → X)
    (F XF : X → ℝ)
    (T : X → ℝ)
    (theta : ℝ)
    (x : X)
    (hgenerator : ∀ t : ℝ,
      HasDerivAt (fun s => F (flow s x)) (XF (flow t x)) t) :
    deriv (fun vartheta => relationalObservable flow F T vartheta x) theta =
      XF (flow (theta - T x) x) := by
  exact (relationalObservable_hasDerivAt
    flow F T theta (XF (flow (theta - T x) x)) x
    (hgenerator (theta - T x))).deriv

end RelationalFlow

/-! ## G. One-dimensional clock primitives and origin freedom -/

theorem linear_clock_primitive
    (c x : ℝ) :
    HasDerivAt (fun t : ℝ => c * t) c x := by
  simpa using (hasDerivAt_id x).const_mul c

/-- Two everywhere-differentiable real clock representatives with the same derivative differ only
by an additive constant. -/
theorem clock_primitives_differ_by_constant
    (F G : ℝ → ℝ)
    (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G)
    (hderiv : ∀ x : ℝ, deriv F x = deriv G x)
    (x y : ℝ) :
    F x - G x = F y - G y := by
  have hdiff : Differentiable ℝ (fun z => F z - G z) := hF.sub hG
  have hzero : ∀ z : ℝ, deriv (fun z => F z - G z) z = 0 := by
    intro z
    rw [deriv_sub (hF z) (hG z), hderiv z, sub_self]
  exact is_const_of_deriv_eq_zero hdiff hzero x y

end RelativeRest
