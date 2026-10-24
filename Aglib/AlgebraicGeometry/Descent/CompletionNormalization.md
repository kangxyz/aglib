# Normalization after completion

Import `Aglib.AlgebraicGeometry.Descent.CompletionNormalization`.
The namespace is `AlgebraicGeometry.Scheme.CompletionNormalization`.

## Surface comparison

Let `A` be a Noetherian local domain of dimension two and let
`f : W → Spec A` be a proper dominant morphism from an integral scheme.
Birationality is expressed by invertibility of the original
`Scheme.functionFieldMap f`. Write

```text
H = AdicCompletion (maximalIdeal A) A
Y = pullback f (completionSpecMap A)
β = pullback.fst f (completionSpecMap A).
```

Assume that `H` is a domain, the actual pullback `Y` is integral, and the stalk
of `Y` at every point outside the original closed fibre is integrally closed.
The latter condition is stated at the original point `y` by

```text
¬ maximalIdeal A ≤ (f (β y)).asIdeal.
```

`finite_normalization_and_isIso_completionComparison` gives finiteness of the
actual generic normalization of `W` and invertibility of the actual comparison
from the generic normalization of `Y` to the completed normalization of `W`.
`normalizationCompletionIso` packages that same comparison as an isomorphism.
Normal completion supplies the domain hypothesis on `H` in the intended
surface-resolution application; the stated comparison needs only this part
once normality of the actual completed model off the closed fibre is given.

No Nagata, excellence, G-ring, coefficient-field, perfectness, or catenarity
hypothesis is imposed on the original `A`. Neither finite lower normalization
nor the desired comparison is supplied as an input.

## Original normalization maps

For an integral scheme `X`, the normalization object is literally
`(X.fromSpecStalk (genericPoint X)).normalization`, with the original
`fromNormalization` map. For a dominant `β : Y → X`,
`normalizationComparison β` maps the actual upper normalization into the
pullback of the actual lower normalization.

Its first projection is `genericNormalizationLift` of the original composite
through `β`; its second projection is the original upper normalization map.
`completionComparison` composes it with the canonical pullback-pasting
isomorphism. `completion_flat_surjective` supplies the flatness and
surjectivity of the original local completion map.
`completionComparison_fst` and `completionComparison_snd` retain
the two original projections. `completionComparison_generic_fst` identifies
the generic arrow using the original `functionFieldMap` of that composite.
The source and target are not replaced by abstractly isomorphic normal models.

## Affine comparison and finiteness

On an original nonempty affine open `U ⊂ W`, put `C = Γ(W,U)`. The literal
completed chart is `H⊗[A]C`, with its original `includeRight` map from `C`.
`tensor_faithfullyFlat` derives faithful flatness of this map. The chart-domain
instance comes from its actual open immersion into the integral pullback `Y`.

The original structural and function-field maps give an injective finite-type
algebraic map `A → C`. `tensor_isNagata` applies complete-base GF2 to the
actual completed chart. This remains within the generically algebraic,
dimension-two supplier; no arbitrary-dimensional finite-type stability is
inferred. `tensor_normalization_finite` gives the actual finite upper
normalization. `affine_normalization_finite` descends finiteness to the
normalization of `C` in its supplied total quotient ring. The source
normalization section maps are transferred by `normalizationObjIso`, including
the empty-open case, to obtain `lowerNormalization_isFinite`.

`exists_normalization_conductor_pow` treats the actual quotient of a finite
normalization by its scalar inclusion. Normality outside a finitely generated
ideal makes this quotient vanish there. Its finite support is the zero locus
of its annihilator, so a power of the ideal is a conductor.
`affineNormalizationEquiv` combines this bound with the original completion
quotient comparison and the canonical conductor theorem in
[`FormalGluing.Normalization`](../../RingTheory/Descent/FormalGluing/Normalization.md).

For the scheme assembly, `completionChartSectionsEquiv` identifies the actual
upper section ring with the completion tensor as an algebra over the original
lower sections. Its coefficient equation follows from the original affine
pullback square. Normal stalks outside the closed fibre are transported through
the original affine stalk isomorphisms. The original completion quotient maps
then supply the conductor data on these actual section rings.

The actual comparison induces a map on the affine pullback sections. Its
linearity follows from its original second-projection equation. After the two
normalization section identifications, this map equals
`integralClosure.flatBaseChangeHom`: any two algebra maps from
`norm(C) ⊂ Frac(C)` into a domain faithfully containing `C` agree after
multiplication by each original nonzero denominator, and hence agree.
The conductor theorem makes this actual section map bijective. The affine
opens cover the target pullback, so the target-local isomorphism criterion
gives the global result. No additional cocycle or local inverse is an input.

## Source correspondence and boundary

The normalization/completion statement and finite-algebra descent order follow
[Stacks, Lemma 54.11.6, tag 0BG9](https://stacks.math.columbia.edu/tag/0BG9).
Complete-base finiteness uses
[Lemma 10.162.8, tag 032W](https://stacks.math.columbia.edu/tag/032W),
[Proposition 10.162.15, tag 0334](https://stacks.math.columbia.edu/tag/0334), and
[Lemma 29.55.11, tag 035S](https://stacks.math.columbia.edu/tag/035S), in the
restricted native GF2 scope described above. These primary statements and the
relevant proof passages were checked on 2026-10-24. The canonical conductor
specialization and original-map assembly correspond to the C2/C3 derivation
at SHA-256 `21c43132a3067d97e350b7adc98a18f0553ea580767505b8bfd43a887520f37b`.

The prescribed normalized point-blowup chain of
[Stacks, Lemma 54.11.7, tag 0BGA](https://stacks.math.columbia.edu/tag/0BGA),
complete-local resolution existence, and spreading local modifications to a
general surface are downstream. They are not asserted by this module.
