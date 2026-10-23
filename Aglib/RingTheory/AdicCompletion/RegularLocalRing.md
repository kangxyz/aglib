# Regularity and the actual maximal-adic completion

Import `Aglib.RingTheory.AdicCompletion.RegularLocalRing`.

For a commutative Noetherian local ring R,
`AdicCompletion.ringKrullDim_maximalIdeal_eq R` proves

```text
ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R.
```

`AdicCompletion.isRegularLocalRing_iff_maximalCompletion R` then proves

```text
IsRegularLocalRing R ↔
  IsRegularLocalRing (AdicCompletion (maximalIdeal R) R).
```

These are the original native completion and algebra map, with their
original maximal ideals. There is no domain, dimension, field, excellence,
or supplied flatness hypothesis.

The explicit `AdicCompletion.isNoetherianRing` theorem supplies
Noetherianity of the completion. Mathlib's
`AdicCompletion.flat_of_isNoetherian` supplies flatness of the native
completion algebra. The native local-hom instance makes the completion's
maximal ideal lie over R's maximal ideal, and flatness supplies going down.
The height formula
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` applies to these
two actual maximal ideals. `AdicCompletion.maximalIdeal_eq_map` makes the
quotient image in its extra height term zero. The native local
height/dimension identity gives the first theorem. Combining it with
`AdicCompletion.spanFinrank_maximalIdeal_eq` and
`isRegularLocalRing_iff` gives the second.

The current consumer is the regularity comparison at the original stalks
of the literal completion base change in
`Aglib.AlgebraicGeometry.Spec.CompletionLocalRing`. That consumer derives
Noetherianity of the two stalks from actual local finite type over the
original Noetherian base and its proved Noetherian completion.

The Lean source at SHA256
`3fa9ff9ddbf4ac120b6fe4f8ea79c42aace147e6333001e4ec1b06bb66285a0c`
passed ordinary native compilation in
`remote-da4109b3125a4c29a549760218865ba3` (source `ce4f0ea1`, 4.3 seconds).
The actual arbitrary-scheme and proper global regularity consumer in
`Spec/CompletionLocalRing.lean`, source
`b4e419fa6c40e7558382f998551955c7b7412b647d2bb9b0ededd1b56c73db87`,
passed the full module in native `remote-d16cd3d8` (source `1e48b383`,
20 seconds). These passes cover their stated completion and geometric
hypotheses. No additional local build, test, replay, diagnostic probe, or
Git operation was run for this evidence update.
The source basis is Aglib HEAD
`8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and Lean 4.34.1, with the
standard theorem budget and no added options. No preservation of normality
or global regularity theorem is asserted here.
