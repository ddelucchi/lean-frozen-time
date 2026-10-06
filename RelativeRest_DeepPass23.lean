import RelativeRest_DeepPass22

/-!
# Relative Rest: deep forced pass 23

Construct the relative action normal line explicitly.

The two action coefficients contain one common mode and one relative mode.  The covector
r(v)=(v_M-v_G)/2 annihilates the common direction C_A and sends the normalized relative direction
D_A to 1.  The linearized fixed-point response factors exactly through this covector.

Thus the quotient of the two-sector scale algebra by the solution-preserving common mode is
canonically a real line, with no chosen complement.
-/

noncomputable section

open Function Set

namespace RelativeRest

def relativeScaleCovector : R2 →ₗ[ℝ] ℝ where
  toFun v := (v.2 - v.1) / 2
  map_add' x y := by
    rcases x with ⟨x1, x2⟩
    rcases y with ⟨y1, y2⟩
    simp
    ring
  map_smul' c x := by
    rcases x with ⟨x1, x2⟩
    simp
    ring

@[simp] theorem relativeScaleCovector_CA :
    relativeScaleCovector CA = 0 := by
  norm_num [relativeScaleCovector, CA]

@[simp] theorem relativeScaleCovector_DA :
    relativeScaleCovector DA = 1 := by
  norm_num [relativeScaleCovector, DA]

theorem relativeScaleCovector_nonzero :
    relativeScaleCovector ≠ 0 := by
  intro hzero
  have h := LinearMap.congr_fun hzero DA
  simp at h

/-- The fixed-point linear response depends only on the relative action coordinate. -/
theorem linearizedActionResponse_factors_relative
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (eta : V)
    (v : R2) :
    linearizedActionResponse eta v =
      (-2 * relativeScaleCovector v) • eta := by
  rcases v with ⟨x, y⟩
  simp [linearizedActionResponse, relativeScaleCovector]
  module

section ResponseKernel

variable {V : Type*}
  [AddCommGroup V] [Module ℝ V] [NoZeroSMulDivisors ℝ V]

/-- For a nonzero surviving carrier, the only invisible action variations are precisely those
with zero relative coordinate. -/
theorem linearizedActionResponse_zero_iff_relative_zero
    (eta : V)
    (heta : eta ≠ 0)
    (v : R2) :
    linearizedActionResponse eta v = 0 ↔
      relativeScaleCovector v = 0 := by
  rw [linearizedActionResponse_factors_relative eta v]
  constructor
  · intro h
    have hcoef :
        -2 * relativeScaleCovector v = 0 :=
      (smul_eq_zero.mp h).resolve_right heta
    linarith
  · intro h
    rw [h]
    simp

theorem linearizedActionResponse_kernel_eq_relative_kernel
    (eta : V)
    (heta : eta ≠ 0) :
    LinearMap.ker (linearizedActionResponse eta) =
      LinearMap.ker relativeScaleCovector := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  exact linearizedActionResponse_zero_iff_relative_zero eta heta v

end ResponseKernel

/-- The intrinsic relative action-normal line is the quotient by the common-mode kernel. -/
noncomputable def relativeActionNormalLine :
    (R2 ⧸ LinearMap.ker relativeScaleCovector) ≃ₗ[ℝ] ℝ :=
  clockQuotientEquivReal
    relativeScaleCovector
    relativeScaleCovector_nonzero

/-- Its normalized unit is forced by the same canonical quotient construction used for the
characteristic clock line. -/
noncomputable def relativeActionNormalUnit :
    R2 ⧸ LinearMap.ker relativeScaleCovector :=
  canonicalClockUnit
    relativeScaleCovector
    relativeScaleCovector_nonzero

@[simp] theorem relativeActionNormalUnit_normalized :
    canonicalClockCovector
        relativeScaleCovector
        relativeScaleCovector_nonzero
        relativeActionNormalUnit = 1 := by
  exact canonicalClockCovector_unit
    relativeScaleCovector
    relativeScaleCovector_nonzero

end RelativeRest
