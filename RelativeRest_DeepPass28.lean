import RelativeRest_DeepPass27

/-!
# Relative Rest: deep forced pass 28

Tie the action-space linearized response directly to the Einstein--Maxwell tensor jet.

The earlier generic theorem showed that the common action mode is killed and the relative mode is
-2 times an arbitrary carrier.  Here the carrier is the Ricci tensor itself.  On shell
Ric=8*pi*T, the relative action mode is therefore exactly the fixed-point tensor jet
J=-2 Ric=-16*pi*T.

This removes the last abstract carrier substitution in the action-module paragraph.
-/

noncomputable section

open Function Set

namespace RelativeRest

/-- The on-shell linearized action response with Ricci tensor as the surviving carrier. -/
def tensorLinearizedActionResponse
    (Ric : Tensor44) :
    R2 →ₗ[ℝ] Tensor44 :=
  linearizedActionResponse Ric

@[simp] theorem tensorLinearizedActionResponse_common
    (Ric : Tensor44) :
    tensorLinearizedActionResponse Ric CA = 0 := by
  exact linearizedActionResponse_CA Ric

theorem tensorLinearizedActionResponse_relative
    (Ric : Tensor44) :
    tensorLinearizedActionResponse Ric DA =
      fun i j => -2 * Ric i j := by
  funext i j
  simp [tensorLinearizedActionResponse,
    linearizedActionResponse, DA]
  ring

/-- Einstein--Maxwell on shell identifies the relative action response with the same tensor jet
obtained by differentiating the scaled field-equation defect. -/
theorem tensorLinearizedActionResponse_relative_eq_jet
    (T Ric : Tensor44)
    (hRic : ∀ i j, Ric i j = 8 * Real.pi * T i j) :
    tensorLinearizedActionResponse Ric DA =
      tensorJet T := by
  rw [tensorLinearizedActionResponse_relative]
  symm
  exact tensorJet_eq_minus_two_Ricci T Ric hRic

/-- Complete action-module-to-fixed-point-jet certificate. -/
theorem action_module_tensor_jet_certificate
    (T Ric : Tensor44)
    (hRic : ∀ i j, Ric i j = 8 * Real.pi * T i j) :
    tensorLinearizedActionResponse Ric CA = 0 ∧
    tensorLinearizedActionResponse Ric DA = tensorJet T := by
  exact
    ⟨tensorLinearizedActionResponse_common Ric,
      tensorLinearizedActionResponse_relative_eq_jet T Ric hRic⟩

end RelativeRest
