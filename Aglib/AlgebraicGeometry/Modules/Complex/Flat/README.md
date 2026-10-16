# Bounded-above flat complexes of scheme module sheaves

The schemes are arbitrary. Flatness means the existing actual
`Scheme.Modules.stalkwiseFlat` property at every module stalk. All complexes
are the original integer-indexed `CochainComplex X.Modules ℤ`; a term bound is
supplied explicitly or retained by the bundled bounded-above complex.

[BoundedPullback](BoundedPullback.lean) proves that cycles of an acyclic,
termwise flat complex are flat by descending from its strict upper bound.
Arbitrary geometric pullback preserves acyclicity of such complexes and
quasi-isomorphisms between two such complexes, with possibly different bounds.
The [ordinary flat-object closure properties](../../Flat/Closure.lean) and
[native cycle-sequence maps](../../../../Algebra/Homology/CochainComplex/Cycles.lean)
are lower inputs. No flatness premise on the scheme morphism is added.

[BoundedAboveReplacement](BoundedAboveReplacement.lean) resolves the actual
underlying module-presheaf complex by projectives and applies exact
sheafification with its original counit. It supplies a termwise flat replacement
with the same strict upper bound, without a projectivity assumption on the
category of sheaves. Its lower [projective presheaf interface](../../Flat/ProjectivePresheaves.lean)
retains the scheme specialization; it makes no arbitrary-site assertion.

[Models](Models.lean) chooses these flat models and original augmentations.
It sheafifies actual projective comparison maps and comparison homotopies.
Original sheaf quasi-isomorphisms induce quasi-isomorphisms between the models,
and these remain quasi-isomorphisms after arbitrary pullback. Exactness of the
forgetful functor to presheaves is not assumed. The actual counit and its
component/naturality equations belong to [ordinary complex sheafification](../Sheafification.lean).

[Resolution](Resolution.lean) reindexes the
[natural-number flat chain resolution](../../Flat/Resolution.lean) into
nonpositive cochain degrees. Its displayed augmentation to the degree-zero
single is a quasi-isomorphism. Pulling back this augmentation remains a
quasi-isomorphism when the original module sheaf has flat stalks.

The results require no Noetherian, affine, quasicoherent or perfectness premise.
They supply the actual models used by [native D− pullback](../../DerivedCategory/Minus/README.md).
