# Completion lifts from original transition-kernel corrections

Let `R` be an arbitrary commutative ring, `I` its original ideal, and `M` an
original `R`-module. Let `N n` be original `R`-modules, with original maps

```lean
F : ∀ n, M →ₗ[R] N n
ρ : ∀ n, N (n + 1) →ₗ[R] N n
```

The map compatibility is `(ρ n).comp (F (n + 1)) = F n`. The zero stage is
subsingleton. The correction hypothesis is exactly

```lean
(ρ n).ker ≤ (I ^ n • (⊤ : Submodule R M)).map (F (n + 1))
```

For each original compatible `x : ∀ n, N n`,
`AdicCompletion.exists_compatible_cauchy_lift` constructs a native adic Cauchy
sequence `a`, with `a 0 = 0` and `F n (a n) = x n` at every stage.

At stage `n`, the error `x (n + 1) - F (n + 1) (a n)` belongs to the original
transition kernel by the two compatibility equations. The correction condition
supplies an actual `c n ∈ IⁿM` mapped to this error. Set
`a (n + 1) = a n + c n`. This gives both the exact next lift and the native
successive-Cauchy condition. Correction witnesses are selected from the actual
submodule image; completed surjectivity is proved by this recursion.

If the original maps also kill `IⁿM`,
`AdicCompletion.exists_compatible_lift` gives an actual `z : AdicCompletion I M`
with the component identity, for every original `n`,

```lean
(I ^ n • (⊤ : Submodule R M)).liftQ (F n) (hkill n)
  (AdicCompletion.eval I M n z) = x n
```

This is the native quotient factor of the original `F n` after the native
completion evaluation. No inverse-limit record, replacement tower or
identification of different ideals is introduced. The ring, module and target
module universes retain the native independent boundaries.

There is no Noetherian, finite-generation, field or completeness assumption.
The result constructs compatible quotient classes; it does not assert
convergence in `M`, uniqueness, or completeness for an arbitrary ideal.
The existing `TowerComparison` theorem has an additional shifted-kernel
condition, and the native completion-surjectivity theorem for a fixed linear
map has a different target. Neither is assumed here.

For geometric applications, deriving the correction condition from original
graded sections, relating the original ideal to a centre, and the actual
formal-functions comparison remain separate obligations. This theorem does
not assume a coefficient field or prove those geometric statements.

## Filtered lifting through the original inclusion

`AdicCompletion.exists_filtered_compatible_lift` additionally takes an original
index `q` and `x q = 0`. It returns

```lean
z : AdicCompletion I ↥(I ^ q • (⊤ : Submodule R M))
```

The image of this `z` under `AdicCompletion.map I` of the actual submodule
inclusion has every original component `x n`, using the same original
`liftQ (F n)` after `eval I M n`. This filtered theorem does not need the zero
stage to be subsingleton: its shifted construction only needs `x q = 0`.

The core recursion starts at zero in `IᵠM`, with shifted target modules
`N (q + n)` and the restrictions of the original `F (q + n)`. The native ideal
power identity `Iⁿ(IᵠM) = I^(q+n)M` puts every original correction in the needed
power of this same submodule. Compatibility down from `q + n` to `n` then
recovers all original components, including those below `q`.

This asserts membership in the image of the actual completion map of the
original inclusion. It does not assert injectivity of that map or identify its
image with a power in a completed ring. Any finite-ideal or Noetherian theorem
needed for such an identification remains a caller obligation.
