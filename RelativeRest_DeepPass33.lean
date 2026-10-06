import RelativeRest_DeepPass32

/-!
# Relative Rest: deep forced pass 33

Derive the Kerr--Newman invariant carrier from the explicit aligned Maxwell field.

In the canonical principal orthonormal frame take
  E = Q (r^2-a^2 cos^2 theta) / Sigma^2,
  B = 2 Q a r cos theta / Sigma^2.
The polynomial identity
  (r^2-a^2 c^2)^2 + (2 a r c)^2 = (r^2+a^2 c^2)^2
forces
  E^2+B^2 = Q^2/Sigma^2.
Consequently the Maxwell invariant square is
  I^2+J^2 = 4 Q^4/Sigma^4
and chi=2(E^2+B^2)=2Q^2/Sigma^2.

This removes the Kerr--Newman carrier formula as a separately inserted scalar identity once the
standard aligned field components are supplied.
-/

noncomputable section

open Function Set

namespace RelativeRest

def knElectric
    (Q r a theta : ℝ) : ℝ :=
  Q * (r^2 - a^2 * (Real.cos theta)^2) /
    (Sigma r a theta)^2

def knMagnetic
    (Q r a theta : ℝ) : ℝ :=
  2 * Q * a * r * Real.cos theta /
    (Sigma r a theta)^2

/-- Polynomial core of the aligned Kerr--Newman field magnitude. -/
theorem kn_field_numerator_identity
    (r a c : ℝ) :
    (r^2 - a^2 * c^2)^2 +
      (2 * a * r * c)^2 =
    (r^2 + a^2 * c^2)^2 := by
  ring

/-- The aligned principal Maxwell magnitude is Q^2/Sigma^2. -/
theorem kn_principal_field_magnitude
    (Q r a theta : ℝ)
    (hsig : Sigma r a theta ≠ 0) :
    (knElectric Q r a theta)^2 +
      (knMagnetic Q r a theta)^2 =
    Q^2 / (Sigma r a theta)^2 := by
  unfold knElectric knMagnetic
  field_simp [hsig]
  unfold Sigma
  ring

/-- Therefore the principal carrier magnitude is chi=2Q^2/Sigma^2. -/
theorem kn_field_chi
    (Q r a theta chi : ℝ)
    (hsig : Sigma r a theta ≠ 0)
    (hchi :
      chi =
        2 * ((knElectric Q r a theta)^2 +
          (knMagnetic Q r a theta)^2)) :
    chi =
      2 * Q^2 / (Sigma r a theta)^2 := by
  rw [hchi, kn_principal_field_magnitude Q r a theta hsig]
  ring

/-- The full electromagnetic invariant square is exactly 4Q^4/Sigma^4. -/
theorem kn_maxwell_invariant_square
    (Q r a theta : ℝ)
    (hsig : Sigma r a theta ≠ 0) :
    (maxwellI
        (knElectric Q r a theta)
        (knMagnetic Q r a theta))^2 +
      (maxwellJ
        (knElectric Q r a theta)
        (knMagnetic Q r a theta))^2 =
    4 * Q^4 / (Sigma r a theta)^4 := by
  rw [maxwell_invariant_square,
    kn_principal_field_magnitude Q r a theta hsig]
  field_simp [hsig]
  ring

/-- The field-derived Kerr--Newman carrier forces the invariant clock rate used by the manuscript. -/
theorem kn_field_forces_clock_rate
    (Q r a theta chi omega : ℝ)
    (hQ : Q ≠ 0)
    (hsig : 0 < Sigma r a theta)
    (hchi :
      chi =
        2 * ((knElectric Q r a theta)^2 +
          (knMagnetic Q r a theta)^2))
    (homega : omega = Real.sqrt chi) :
    omega =
      Real.sqrt 2 * |Q| / Sigma r a theta := by
  have hsig0 : Sigma r a theta ≠ 0 := ne_of_gt hsig
  have hcarrier :
      chi = 2 * Q^2 / (Sigma r a theta)^2 :=
    kn_field_chi Q r a theta chi hsig0 hchi
  exact kerrNewman_clock_rate_from_chi
    Q (Sigma r a theta) chi omega
    hQ hsig hcarrier homega

end RelativeRest
