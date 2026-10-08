# Einstein–Maxwell intrinsic clock: adversarial proof ledger

This is a **proof-obligation ledger**, not a declaration that every claim has been proved.
It documents which inferences follow from supplied fields, which statements are
conditional on geometric data, and where an attempted unconditional theorem is false.

## Parent certificate actually inspected

- Source: `RelativeRest_OneFile_Certificate.lean`, blob `4850e6a5eac060cfa3d624836cf95cbdfcbe2c39` on `formalize-forced-chain`.
- Source size: 35,861 lines, about 1.37 million decoded characters.
- It has over 1,500 declarations beginning with `theorem`, including actual
  arbitrary-field Maxwell stress/Rainich algebra, Einstein–Maxwell local first-variation
  identities, Kerr–Newman potential-to-field computations, Christoffel/Ricci component
  calculations, and a full metric-source identity on the regular Kerr–Newman chart.
- **Zero project-local declarations beginning `axiom`, `constant`, `opaque`,
  `sorry`, or `admit` were located in the retrieved source.** This is a
  *syntactic inspection*, not a successful Lean kernel execution or a demonstration
  that every theorem has the intended physical content.
- Existing GitHub Actions for this head and the new feature branch report failure
  and expose no executed compiler steps. Do not label the head kernel-verified
  without a real `lake build` and `#print axioms` audit.

## A. The new action → field → stress → relative jet chain

`RelativeRest_Maxwell_Action.lean`:
1. A first jet `D_a A_b` yields `F_ab=D_a A_b-D_b A_a`; skew symmetry is proved.
2. Symmetric gauge Hessians leave `F`, the Maxwell Lagrangian, and its stress invariant.
3. The Maxwell kinetic density has an exact quadratic variation, not a postulated
   first-order law.

`RelativeRest_Maxwell_StressScaling.lean`:
4. The covariant Maxwell stress is built by contracting a completely arbitrary
   four-dimensional two-form with the inverse metric.
5. Independent constant metric/potential scalings give the exact tensor identity
   `T_ab[rho^2 g,lambda F]=(lambda^2/rho^2)T_ab[g,F]`.
6. If some stress component is nonzero and that component is preserved, positive
   `rho,lambda` must coincide.
7. The physical `1/(4*pi)` factor is restored separately so no source-normalization
   ambiguity enters the Einstein equation.

`RelativeRest_FieldDerivedJet.lean`:
8. Given the explicitly quantified on-shell Einstein equation
   `G_ab=8*pi*T_ab[F]`, the relative residual
   `G_ab-exp(2s)*8*pi*T_ab[F]` has its unique zero at `s=0` whenever the
   stress witness is nonzero.
9. Its **first derivative**, without an inserted jet hypothesis, is
   `J_ab=-16*pi*T_ab[F]`.
10. An exact component expansion recovers tracelessness and
    `T_00=(E^2+B^2)/(8*pi)`; a nonzero electric jet supplies the necessary
    nonzero-stress witness.
11. The residual is gauge invariant under potential shifts by symmetric Hessians.
12. In vacuum, `F=0,G=0`, the residual is identically zero for *all* rapidities.
    Universal relative-fixed-point uniqueness is therefore mathematically false
    without a nonzero-carrier restriction.

`RelativeRest_ActionToJetBridge.lean`:
13. The arbitrary-field tensor `generalMaxwellF` in the **existing 35k-line
    certificate** is realized by a literal local potential jet `D=F/2`.
14. The physical Maxwell stress calculated from that jet is proved componentwise
    equal to the parent's `generalMaxwellStressCovFromF`.
15. The parent's already-formalized inverse-metric action derivative is therefore
    `-T_ab[F]/2` for *the same F*, preventing an independent stress-definition
    substitution in the action → Einstein-relative-jet chain.

**Important distinction:** The main certificate already derives several of these
relations in different conventions; the bridge makes their **definitional
compatibility** explicit. It is a strengthening of the audit trail, not a
claim that their content was absent from the parent file.

## B. Frame, isotropy, and the meaning of intrinsic

`IntrinsicBoostScope` proves a nontrivial Lorentz boost fixes no nonzero
null-plane vector. Thus even a fully field-derived, non-null Rainich involution
does not intrinsically pick a timelike observer if its complete geometric jet
retains continuous boost isotropy.

The largest certificate correctly distinguishes the finite-resolving-jet
branch from the branch in which the full boost stabilizer remains all of
`SO^+(1,1)`. Its theorem `einsteinMaxwell_entireFormalizedPaper_forced`
contains exactly that disjunction. **The second alternative cannot be
silently turned into a unique clock.**

Needed to promote a local observer to a canonical scalar clock:
- non-null Maxwell carrier;
- a field-derived first or higher jet that actually breaks boost isotropy;
- orientation/time-orientation compatible normalizations;
- a regular optical endpoint branch with the required nondegeneracy.

## C. Synchronization: mathematical uniqueness is NOT curl cancellation

`RelativeRest_SynchronizationScope.lean` constructs affine one-forms on R²:
- `T_O = -dt + t dx`, so `dT_O=dt∧dx`.
- `beta_c = x dt + c*x dx`, for arbitrary `c∈R`.
- Every `beta_c` has `d beta_c=-dT_O`, vanishes along the same
  reference curve `x=0`, and makes `T_O+beta_c` closed.
- Distinct `c` give distinct corrections.

Therefore `d beta=-dT_O` together with `beta|gamma=0` **cannot**
by themselves yield a unique synchronization correction.

The same module positively proves uniqueness **when the complete optical
gradient is supplied**:
`beta=dTheta_optical-T_O` is then the unique solution of that equation.
For the paper's claim of intrinsically forced synchronization, the
geometric work is to prove the appropriate null endpoint/eikonal `Theta`
is intrinsic and unique on the designated regular neighborhood. The
parent source handles finite-dimensional regular Synge endpoint interfaces,
but does not prove existence for every electrovac spacetime.

## D. Scope of the largest source's global-sounding headline theorems

At roughly lines 34,269–34,525, the largest source declares several
`einsteinMaxwell_*_entireFormalizedPaper_forced` theorems. Their quantified
inputs **still include** some of:

- `S : RegularSyngeEndpointPairSource Bdual`;
- `hnonnull : generalMaxwellNonNull ...`;
- a first-jet non-null resolver (`hp`) or `T : MaxwellFiniteResolverTower ...`;
- `hind : S.EndpointPairIndependent` and bilinear symmetry;
- independently parameterized Kerr–Newman data, on which the theorem
  conjoins a separate Kerr–Newman certificate.

Those are honest **conditional theorems** about the regular branch and a
separate specialization. Merely packaging their conjunction is not a
proof that the regular branch or field-derived resolver exists in every
Einstein–Maxwell solution, nor that the Kerr data are identified with
the same arbitrary electrovac field.

## E. Remaining true first-principles infrastructure

1. Build the curved Lorentzian manifold/connection/volume/field bundle with
   enough differential geometry to **derive** the Euler–Lagrange equations
   of the full action as identities of geometric variations, with relevant
   boundary and falloff hypotheses. A frame-level pointwise computation does
   not, by itself, prove a global functional-analytic variational theorem.
2. Construct the **actual** covariant presymplectic and Noether current
   from that action, with careful distinction among off-shell variations,
   tangent vectors to the solution space, compactly supported gauge
   directions, and surface charges. In particular, a genuinely degenerate
   pure gauge direction cannot be assumed simultaneously to generate
   a nonzero bulk symplectic pairing without clarifying the domain and
   boundary compensation.
3. Construct the regular Synge endpoints from the specific conformal
   Lorentzian metric, prove a local uniqueness/regularity theorem, and
   demonstrate that the produced optical gradient matches the claimed
   `T_O+beta`. The algebraic correction theorem needs this input.
4. Prove the boost rigidity hypotheses from the actual field jet where they
   hold, and state what survives on fully isotropic or null branches.
5. Integrate the local clock (or specify its anholonomic/endpoint
   interpretation) with domain and topological hypotheses, rather than
   treating a non-closed local covector as the gradient of a scalar.
6. Run the pinned Lean kernel over the full combined import graph, inspect
   `#print axioms` outputs, and stress-test the meaning of every headline
   theorem's quantified premises.

## F. Reproducible checks

```bash
lake update
lake exe cache get
lake build RelativeRest_Maxwell_StressScaling
lake build RelativeRest_FieldDerivedJet
lake build RelativeRest_SynchronizationScope
lake build RelativeRest_OneFile_Certificate
lake build RelativeRest_ActionToJetBridge
lake env lean RelativeRest_OneFile_Certificate.lean
```

The existing workflow also archives the build logs for the independent new
modules. **No release or PR merge should be asserted until those jobs really
execute successfully.**
