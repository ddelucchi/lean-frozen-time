import RelativeRest_DeepPass33

/-!
# Relative Rest: deep forced pass 34

Derive the fixed-point Rainich scalar directly from arbitrary-frame Maxwell invariants.

The existing emMixed matrix is the conventional Maxwell mixed stress with the overall 1/(4*pi)
removed.  Hence the fixed-point mixed jet J=-16*pi*T is exactly -4 emMixed.  The already-proved
arbitrary-frame Maxwell stress square then forces
  J^2 = (I^2+J_EM^2) Id
componentwise.

Thus the scalar that normalizes the fixed-point carrier is not an additional Rainich datum:
its square is exactly the standard Maxwell invariant norm.
-/

noncomputable section

open Function Set
open scoped BigOperators

namespace RelativeRest

/-- The standard Maxwell invariant norm square is sixteen times the stress Rainich scalar. -/
theorem maxwellInvariantSquare_eq_sixteen_rainich
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    (maxwellI
        (Real.sqrt (e1^2 + e2^2 + e3^2))
        (Real.sqrt (b1^2 + b2^2 + b3^2)))^2
      +
      (-4 * (e1*b1 + e2*b2 + e3*b3))^2
      =
    16 * emRainichScalar e1 e2 e3 b1 b2 b3 := by
  unfold maxwellI emRainichScalar
  have hE :
      (Real.sqrt (e1^2 + e2^2 + e3^2))^2 =
        e1^2 + e2^2 + e3^2 := by
    rw [Real.sq_sqrt]
    positivity
  have hB :
      (Real.sqrt (b1^2 + b2^2 + b3^2))^2 =
        b1^2 + b2^2 + b3^2 := by
    rw [Real.sq_sqrt]
    positivity
  rw [hE, hB]
  ring

/-- Coordinate-free-looking invariant norm written directly in arbitrary-frame components. -/
def emInvariantNormSq
    (e1 e2 e3 b1 b2 b3 : ℝ) : ℝ :=
  4 *
    (b1^2 + b2^2 + b3^2 -
      (e1^2 + e2^2 + e3^2))^2 +
  16 * (e1*b1 + e2*b2 + e3*b3)^2

theorem emInvariantNormSq_eq_sixteen_rainich
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    emInvariantNormSq e1 e2 e3 b1 b2 b3 =
      16 * emRainichScalar e1 e2 e3 b1 b2 b3 := by
  unfold emInvariantNormSq emRainichScalar
  ring

theorem emInvariantNormSq_nonneg
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    0 ≤ emInvariantNormSq e1 e2 e3 b1 b2 b3 := by
  unfold emInvariantNormSq
  positivity

theorem emInvariantNormSq_pos_of_nonnull
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (hn : ¬ (b1^2 + b2^2 + b3^2 =
        e1^2 + e2^2 + e3^2 ∧
      e1*b1 + e2*b2 + e3*b3 = 0)) :
    0 < emInvariantNormSq e1 e2 e3 b1 b2 b3 := by
  rw [emInvariantNormSq_eq_sixteen_rainich]
  have hR :=
    emRainichScalar_pos_of_nonnull
      e1 e2 e3 b1 b2 b3 hn
  positivity

/-- The fixed-point mixed jet J=-16*pi*T=-4 emMixed in the normalization of emMixed. -/
def emJetMixed
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    Tensor44 :=
  fun i j =>
    -4 * emMixed e1 e2 e3 b1 b2 b3 i j

/-- The arbitrary-frame fixed-point jet satisfies the Rainich square with scalar equal to the
Maxwell invariant norm square. -/
theorem emJetMixed_rainich_square
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (i j : Fin 4) :
    (∑ k : Fin 4,
      emJetMixed e1 e2 e3 b1 b2 b3 i k *
      emJetMixed e1 e2 e3 b1 b2 b3 k j) =
      (if i = j then
        emInvariantNormSq e1 e2 e3 b1 b2 b3
       else 0) := by
  have hscale :
      (∑ k : Fin 4,
        emJetMixed e1 e2 e3 b1 b2 b3 i k *
        emJetMixed e1 e2 e3 b1 b2 b3 k j) =
      16 *
        (∑ k : Fin 4,
          emMixed e1 e2 e3 b1 b2 b3 i k *
          emMixed e1 e2 e3 b1 b2 b3 k j) := by
    unfold emJetMixed
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hscale,
    emMixed_rainich_square
      e1 e2 e3 b1 b2 b3 i j]
  by_cases hij : i = j
  · simp [hij, emInvariantNormSq_eq_sixteen_rainich]
  · simp [hij]

/-- The positive carrier magnitude is the square root of the Maxwell invariant norm. -/
def emCarrierMagnitude
    (e1 e2 e3 b1 b2 b3 : ℝ) : ℝ :=
  Real.sqrt
    (emInvariantNormSq e1 e2 e3 b1 b2 b3)

theorem emCarrierMagnitude_sq
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    (emCarrierMagnitude
      e1 e2 e3 b1 b2 b3)^2 =
      emInvariantNormSq e1 e2 e3 b1 b2 b3 := by
  unfold emCarrierMagnitude
  exact Real.sq_sqrt
    (emInvariantNormSq_nonneg
      e1 e2 e3 b1 b2 b3)

theorem emCarrierMagnitude_pos_of_nonnull
    (e1 e2 e3 b1 b2 b3 : ℝ)
    (hn : ¬ (b1^2 + b2^2 + b3^2 =
        e1^2 + e2^2 + e3^2 ∧
      e1*b1 + e2*b2 + e3*b3 = 0)) :
    0 <
      emCarrierMagnitude
        e1 e2 e3 b1 b2 b3 := by
  unfold emCarrierMagnitude
  exact Real.sqrt_pos.2
    (emInvariantNormSq_pos_of_nonnull
      e1 e2 e3 b1 b2 b3 hn)

end RelativeRest
