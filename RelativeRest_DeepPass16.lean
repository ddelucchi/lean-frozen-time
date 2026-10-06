import RelativeRest_DeepPass15

/-!
# Relative Rest: deep forced pass 16

Construct the characteristic descendant from kernel invisibility alone.

The manuscript does not need a separately supplied covector on the characteristic image.  If a
parameter response ell vanishes whenever the characteristic map beta vanishes, then ell factors
uniquely through im(beta).  This file constructs that factorization using the quotient universal
property and the canonical equivalence P/ker(beta) ~= im(beta).

Thus surjectivity is no longer an assumption: the target is literally im(beta).
-/

noncomputable section

open Function Set

namespace RelativeRest

section ForcedRangeDescent

variable {P K : Type*}
  [AddCommGroup P] [Module ℝ P]
  [AddCommGroup K] [Module ℝ K]

/-- The canonical map from the parameter space onto the image of beta is surjective by definition. -/
theorem rangeRestrict_surjective
    (beta : P →ₗ[ℝ] K) :
    Function.Surjective beta.rangeRestrict := by
  intro y
  rcases y.property with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  exact hp

/-- Kernel invisibility constructs the unique response covector on im(beta). -/
noncomputable def descendantOnRange
    (beta : P →ₗ[ℝ] K)
    (ell : P →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker beta ≤ LinearMap.ker ell) :
    LinearMap.range beta →ₗ[ℝ] ℝ :=
  ((LinearMap.ker beta).liftQ ell hker).comp
    (LinearMap.quotKerEquivRange beta).symm.toLinearMap

theorem descendantOnRange_apply
    (beta : P →ₗ[ℝ] K)
    (ell : P →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker beta ≤ LinearMap.ker ell)
    (p : P) :
    descendantOnRange beta ell hker (beta.rangeRestrict p) = ell p := by
  have hrange :
      LinearMap.quotKerEquivRange beta
          (Submodule.Quotient.mk p) =
        beta.rangeRestrict p := by
    apply Subtype.ext
    exact LinearMap.quotKerEquivRange_apply_mk beta p
  change
    (LinearMap.ker beta).liftQ ell hker
        ((LinearMap.quotKerEquivRange beta).symm
          (beta.rangeRestrict p)) =
      ell p
  rw [← hrange]
  simp

theorem descendantOnRange_factorization
    (beta : P →ₗ[ℝ] K)
    (ell : P →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker beta ≤ LinearMap.ker ell) :
    (descendantOnRange beta ell hker).comp beta.rangeRestrict = ell := by
  ext p
  exact descendantOnRange_apply beta ell hker p

/-- No second covector on im(beta) can induce the same parameter response. -/
theorem descendantOnRange_unique
    (beta : P →ₗ[ℝ] K)
    (ell : P →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker beta ≤ LinearMap.ker ell)
    (Lambda : LinearMap.range beta →ₗ[ℝ] ℝ)
    (hLambda : Lambda.comp beta.rangeRestrict = ell) :
    Lambda = descendantOnRange beta ell hker := by
  exact descended_covector_unique
    beta.rangeRestrict
    (rangeRestrict_surjective beta)
    ell
    Lambda
    (descendantOnRange beta ell hker)
    hLambda
    (descendantOnRange_factorization beta ell hker)

end ForcedRangeDescent

/-! ## B. Minimal characteristic-response data -/

section MinimalCharacteristicResponse

variable {P K : Type*}
  [AddCommGroup P] [Module ℝ P]
  [AddCommGroup K] [Module ℝ K]

/-- The minimal linear data needed for the manuscript's characteristic descent. -/
structure CharacteristicResponseData where
  beta : P →ₗ[ℝ] K
  ell : P →ₗ[ℝ] ℝ
  kernel_invisible : LinearMap.ker beta ≤ LinearMap.ker ell
  ell_positive : ∃ p : P, 0 < ell p

/-- The characteristic covector is constructed, not supplied. -/
noncomputable def characteristicLambda
    (D : CharacteristicResponseData (P:=P) (K:=K)) :
    LinearMap.range D.beta →ₗ[ℝ] ℝ :=
  descendantOnRange D.beta D.ell D.kernel_invisible

theorem characteristicLambda_factorization
    (D : CharacteristicResponseData (P:=P) (K:=K)) :
    (characteristicLambda D).comp D.beta.rangeRestrict = D.ell := by
  exact descendantOnRange_factorization
    D.beta D.ell D.kernel_invisible

theorem characteristicEll_nonzero
    (D : CharacteristicResponseData (P:=P) (K:=K)) :
    D.ell ≠ 0 := by
  rcases D.ell_positive with ⟨p, hp⟩
  intro hzero
  rw [hzero] at hp
  simp at hp

theorem characteristicLambda_nonzero
    (D : CharacteristicResponseData (P:=P) (K:=K)) :
    characteristicLambda D ≠ 0 := by
  intro hzero
  apply characteristicEll_nonzero D
  have hfac := characteristicLambda_factorization D
  rw [hzero] at hfac
  simpa using hfac.symm

/-- The stress-visible characteristic quotient is therefore forced to be a real line. -/
noncomputable def characteristicClockLine
    (D : CharacteristicResponseData (P:=P) (K:=K)) :
    (LinearMap.range D.beta ⧸
      LinearMap.ker (characteristicLambda D)) ≃ₗ[ℝ] ℝ :=
  clockQuotientEquivReal
    (characteristicLambda D)
    (characteristicLambda_nonzero D)

end MinimalCharacteristicResponse

end RelativeRest
