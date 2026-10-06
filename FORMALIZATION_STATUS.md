# Formalization status: Relative Rest

This branch is an adversarial formal-verification companion to *Relative Rest as the Resolution of Frozen Time in Einstein–Maxwell Theory*.

## Current source-level audit

- Lean source modules: one base certificate plus deep passes 2–11.
- More than 200 theorem/lemma declarations are present.
- Project-local `sorry`: 0.
- Project-local `admit`: 0.
- Project-local `axiom` declarations: 0.
- Project-local `opaque` declarations: 0.
- The old `BridgeData` interface that supplied factorization/nonvanishing has been removed.
- The old tautological relational-evolution interface has been removed.
- `RelativeRest_Audit.lean` prints axiom dependencies for the headline theorems once the project is kernel-checked.

## What is now derived inside the project

The formal source derives, rather than merely states, the following logical layers:

1. Projective relative coordinate, exchange law, Möbius composition, and fixed-point uniqueness.
2. Exact four-dimensional reciprocity of the Einstein–Hilbert and Maxwell relative weights.
3. Solution-preserving relative fixed point and the nonzero first defect jet.
4. Action-space boost algebra and normalized action-to-optical intertwiner.
5. Arbitrary-orthonormal-frame Maxwell stress square (Rainich algebra), non-null positivity, and null-boundary nilpotence.
6. Involution projectors and the algebraic principal-plane split.
7. Existence and uniqueness of the residual boost balance, including the explicit root `sigmaStar`.
8. Starting-dyad covariance and balanced-dyad invariance.
9. Homogeneous conformal-factor uniqueness in the stated carrier-algebraic category.
10. Characteristic-covector factorization, uniqueness, nonvanishing from a positive response witness, and the one-dimensional quotient.
11. Local clock covector and normalization derived directly from `T_O=-omega g(u,.)`, not supplied independently.
12. Unique normalized local/global clock-line isomorphism.
13. Null-pair optical closure, radar midpoint/radius uniqueness, common-origin freedom, and synchronization cancellation.
14. Relational evolution under intrinsic clock translation for an actual differentiable flow parameter.
15. Kerr–Newman radial carrier derivative `d_r log chi=-4r/Sigma`.
16. Boyer–Lindquist principal-null algebra, zero-boost midpoint, unit Carter observer, and Carter angular velocity.
17. Field-derived Kerr–Newman radial responses, `sigmaStar=0`, and the carrier-to-Carter chain.
18. Kerr–Newman curvature-to-clock-to-Mino chain.
19. Causal endpoint sup/inf globalization and monotonicity from transitivity/push-up.
20. Pointwise Einstein–Maxwell jet contraction giving exactly
    `(1/(8*pi)) eps·J·xi = -2 eps·T·xi`.
21. Homogeneous clock-cover canonical-pair algebra and fixed-point jet stabilizer logic.

## Remaining first-principles geometric infrastructure

The branch does **not** currently claim that the following are reconstructed from foundational manifold definitions in Lean:

1. The full curved Lorentzian manifold/Levi-Civita/Ricci infrastructure needed to derive the Einstein tensor and the Einstein–Maxwell equations from the action.
2. The general Iyer–Wald covariant phase-space variational identity itself. The paper-specific Einstein–Maxwell response coefficient downstream of that identity is formalized.
3. The differential-geometric contact/characteristic quotient theorem in full manifold generality. Its one-dimensional quotient, normalization, homogeneous clock-cover, and uniqueness algebra are formalized.
4. Synge world-function existence/smoothness and the implicit differentiation theorem yielding the null eikonal gradients in curved spacetime.
5. A foundational proof that the displayed Kerr–Newman null pair is the repeated principal null pair of the full curvature tensor. Its Boyer–Lindquist nullity, midpoint, normalization, carrier balance, and Carter identification are formalized.

These remaining items are explicit proof-frontier items, not hidden assumptions.

## Kernel-execution status

The repository is pinned to Lean 4.34.1 and mathlib 4.34.1. During this pass, GitHub Actions jobs, including a one-line runner smoke test, terminated before runner allocation with no executed steps. Consequently the new deep-pass modules are **not yet claimed to have been kernel-checked in this session**. The source is intentionally labeled as source-level formalization until a real Lean process runs it.

A referee-facing release should not be tagged until `lake build` succeeds and `RelativeRest_Audit.lean` has been inspected.
