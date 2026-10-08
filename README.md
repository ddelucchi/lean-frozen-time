# Einstein–Maxwell intrinsic-clock Lean formalization

All formal proof declarations live in exactly one source file:

**[RelativeRest_OneFile_Certificate.lean](RelativeRest_OneFile_Certificate.lean)**

The entire original 35,861-line certificate and every subsequently integrated Maxwell-action,
tensor-scaling, stress-variation, relative-jet, and synchronization audit theorem are in that file.

The repository uses `lakefile.toml` (not `lakefile.lean`) to avoid a second Lean source.

```sh
lake update
lake exe cache get
lake build RelativeRest_OneFile_Certificate
```

No separate Lean proof modules or imports beyond Mathlib. Passing the Lean kernel build,
including the inline `#print axioms` audit, is required before claiming proof verification.
A theorem with explicit non-null, endpoint, or jet-resolution premises proves a conditional
result; it does not prove those premises for every Einstein–Maxwell solution.
