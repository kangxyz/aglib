# The original homothety of the coinduced regular coefficient

For a commutative ring `S : Type u` and an actual complex
`J : CochainComplex (ModuleCat.{u} S) ℤ`, `homothety J` is the map

`S[0] → Hom_S(J,J)`

obtained by composing the existing signed evaluation at `S[0]` with
precomposition by `(regularSingleComplexIso J).inv`. The latter is the
existing inverse of evaluation at one. Neither comparison is rebuilt.
`homothety_f_zero_v_apply` proves that a scalar `s` maps to the cochain
acting as `x ↦ s • x` in every degree of `J`. The sign in the original
evaluation is one because the regular source sits in degree zero.

Let `q:R→S` be a map of commutative rings in universe `u`, with `R`
regular local of specified finite dimension `d`. Suppose the actual
restricted regular `S` module is finite over `R`. For an actual
K-injective coefficient complex `I`, a quasi-isomorphism `R[0]→I`, and
K-injective coinduced complex `J`,
`homothety_coinduced_quasiIso_of_restrictFinite` proves that this exact
homothety is a quasi-isomorphism. Its proof reuses
`derivedEvaluation_single_isIso_of_restrictFinite` from `TwoLayer`, which
already constructs the finite-projective model internally using
`RegularLocalRing/FiniteComplexModel` and applies `Perfect`. Native
naturality through the single-object isomorphism and
`derivedEvaluation_app_Q` recover the same chain-level map.

`homothety_coinduced_injectiveResolution_quasiIso` specializes this result
to any actual injective resolution of the regular base. The original
resolution augmentation and both required K-injectivity facts are then
supplied internally by the native resolution and exact
restriction/coinduction adjunction.

No projectivity or flatness of `S` over `R`, local property of `S`, normality,
dimension bound on `S`, supplied perfect model, homothety isomorphism,
canonical trivialization, or resolution of singularities is assumed.
The result concerns the actual coinduced coefficient complex, not an
arbitrary module merely named canonical or dualizing.

The normal-quotient canonical-module construction is the immediate
application. Comparing this coinduced coefficient to the installed D+
object and then its concentrated canonical homology must preserve the
existing maps and source action. That transport, and a genuine local
dualizing-uniqueness or Bass theorem for the reverse intrinsic Gorenstein
criterion, are not proved here. The mathematical homothety condition is
the third, separate condition in
[Stacks, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B).
