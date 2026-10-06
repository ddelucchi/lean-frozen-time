import RelativeRest_DeepPass13

/-!
# Relative Rest: deep forced pass 14

Remove two remaining algebraic freedoms used in the manuscript:

* the normalized action-to-optical identification is not merely exhibited; it is the unique
  linear map carrying the forced even/odd action basis to the forced even/odd optical basis;
* the clock-transport integrability criterion is lifted from scalar placeholders to arbitrary
  tensor/vector modules, so vanishing projected curvature is equivalent to vanishing vorticity
  and the forced acceleration-gradient balance.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-! ## A. Uniqueness of the normalized action-to-optical map -/

def actionToOpticalLinear : R2 →ₗ[ℝ] R2 where
  toFun := actionToOptical
  map_add' x y := by
    rcases x with ⟨x1, x2⟩
    rcases y with ⟨y1, y2⟩
    ext <;> simp [actionToOptical] <;> ring
  map_smul' c x := by
    rcases x with ⟨x1, x2⟩
    ext <;> simp [actionToOptical] <;> ring

@[simp] theorem actionToOpticalLinear_apply
    (v : R2) :
    actionToOpticalLinear v = actionToOptical v := rfl

@[simp] theorem actionToOpticalLinear_CA :
    actionToOpticalLinear CA = TO := by
  exact actionToOptical_CA

@[simp] theorem actionToOpticalLinear_DA :
    actionToOpticalLinear DA = RO := by
  exact actionToOptical_DA

/-- CA and DA form the normalized action basis, so their forced optical images determine the
entire linear identification uniquely. -/
theorem actionToOpticalLinear_unique
    (I : R2 →ₗ[ℝ] R2)
    (hC : I CA = TO)
    (hD : I DA = RO) :
    I = actionToOpticalLinear := by
  ext v
  rcases v with ⟨x, y⟩
  have hv :
      (x, y) =
        ((x + y) / 2 : ℝ) • CA +
        ((y - x) / 2 : ℝ) • DA := by
    ext <;> simp [CA, DA] <;> ring
  change I (x, y) = actionToOptical (x, y)
  rw [hv, map_add, map_smul, map_smul, hC, hD]
  ext <;> simp [actionToOptical, TO, RO] <;> ring

theorem actionToOpticalLinear_intertwines_generator
    (v : R2) :
    actionToOpticalLinear (YA v) =
      BO (actionToOpticalLinear v) := by
  exact actionToOptical_intertwines_generator v

theorem actionToOpticalLinear_intertwines_exchange
    (v : R2) :
    actionToOpticalLinear (JA v) =
      JO (actionToOpticalLinear v) := by
  exact actionToOptical_intertwines_exchange v

theorem actionToOpticalLinear_intertwines_boost
    (s : ℝ) (v : R2) :
    actionToOpticalLinear (actionBoost s v) =
      opticalBoost s (actionToOpticalLinear v) := by
  exact actionToOptical_intertwines_boost s v

/-! ## B. Tensor-valued clock transport and integrability -/

section TensorClockTransport

variable {V : Type*}
  [AddCommGroup V] [Module ℝ V] [NoZeroSMulDivisors ℝ V]

/-- Purely spatial part of dT_O = -d(omega u^flat). -/
def spatialClockCurvature
    (omega : ℝ) (varpi : V) : V :=
  (-2 * omega) • varpi

/-- Mixed timelike/spatial part of dT_O. -/
def mixedClockCurvature
    (omega : ℝ) (accel gradLogK : V) : V :=
  (-omega) • (accel + (1 / 4 : ℝ) • gradLogK)

theorem spatialClockCurvature_zero_iff
    (omega : ℝ) (varpi : V)
    (homega : omega ≠ 0) :
    spatialClockCurvature omega varpi = 0 ↔ varpi = 0 := by
  unfold spatialClockCurvature
  have hcoef : -2 * omega ≠ 0 :=
    mul_ne_zero (by norm_num) homega
  constructor
  · intro h
    exact (smul_eq_zero.mp h).resolve_left hcoef
  · rintro rfl
    simp

theorem mixedClockCurvature_zero_iff
    (omega : ℝ) (accel gradLogK : V)
    (homega : omega ≠ 0) :
    mixedClockCurvature omega accel gradLogK = 0 ↔
      accel = -(1 / 4 : ℝ) • gradLogK := by
  unfold mixedClockCurvature
  have hcoef : -omega ≠ 0 := neg_ne_zero.mpr homega
  constructor
  · intro h
    have hsum :
        accel + (1 / 4 : ℝ) • gradLogK = 0 :=
      (smul_eq_zero.mp h).resolve_left hcoef
    exact eq_neg_of_add_eq_zero_left hsum
  · intro h
    rw [h]
    simp

/-- The complete projected clock curvature vanishes exactly under the two manuscript transport
conditions.  This is the tensor/module version of the scalar certificate. -/
theorem clockTransport_zero_iff
    (omega : ℝ)
    (varpi accel gradLogK : V)
    (homega : omega ≠ 0) :
    (spatialClockCurvature omega varpi = 0 ∧
      mixedClockCurvature omega accel gradLogK = 0) ↔
    (varpi = 0 ∧
      accel = -(1 / 4 : ℝ) • gradLogK) := by
  constructor
  · rintro ⟨hsp, hmix⟩
    exact
      ⟨(spatialClockCurvature_zero_iff
          omega varpi homega).mp hsp,
       (mixedClockCurvature_zero_iff
          omega accel gradLogK homega).mp hmix⟩
  · rintro ⟨hvarpi, haccel⟩
    exact
      ⟨(spatialClockCurvature_zero_iff
          omega varpi homega).mpr hvarpi,
       (mixedClockCurvature_zero_iff
          omega accel gradLogK homega).mpr haccel⟩

/-- The weaker spatial/Frobenius obstruction vanishes exactly when vorticity vanishes. -/
theorem frobeniusSpatialObstruction_zero_iff
    (omega : ℝ) (varpi : V)
    (homega : omega ≠ 0) :
    spatialClockCurvature omega varpi = 0 ↔ varpi = 0 :=
  spatialClockCurvature_zero_iff omega varpi homega

end TensorClockTransport

end RelativeRest
