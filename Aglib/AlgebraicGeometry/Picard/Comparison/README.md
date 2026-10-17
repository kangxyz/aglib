# Rigidification and the fppf comparison map

This family compares the Picard functors of [Picard](../README.md) with the rigidified functor
and with the fppf sheafification (plan row F7, target 4 of
[PICARD_PLAN.md](../../../../doc/PICARD_PLAN.md)). It follows Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Thm 2.5 with Def. 2.8 and Lemmas 2.9, 2.10 (pp. 18–19), and
[Stacks 0B9N](https://stacks.math.columbia.edu/tag/0B9N). Declarations live in the native
namespaces `AlgebraicGeometry.Scheme.RelativePicard` and, for the module-sheaf facts,
`AlgebraicGeometry.Scheme.Modules`. All objects are the committed Picard functors, Mathlib's
`Scheme.Modules.pullback`, and Mathlib's sheafification for `Scheme.fppfTopology.over S`.

## Leaves

[Endomorphisms](Endomorphisms.lean), imported as
`Aglib.AlgebraicGeometry.Picard.Comparison.Endomorphisms`, has no hypothesis on the schemes:

- `pullback_map_globalScalarEndomorphism`: `(pullback f).map (globalScalarEndomorphism Y M a) =
  globalScalarEndomorphism X ((pullback f).obj M) (f.appTop a)`, with the pushforward form
  `pushforward_map_globalScalarEndomorphism`;
- `globalScalarEndomorphism_mul`, `_one`, `_conj`, and `globalScalarIso M a` for a global unit;
- `eq_unitMul_unitHomGlobalSectionsEquiv` (every endomorphism of the structure module is
  `unitMul` of its value at `1`), `unitIsoGlobalUnit` (the unit of an automorphism of the
  structure module), `globalScalarEndomorphism_injective_of_iso` (global functions act
  faithfully on a module isomorphic to the structure module);
- `exists_eq_globalScalarEndomorphism_of_isLocallyRankOne`: every endomorphism of a locally
  rank-one module sheaf is multiplication by a global function.

These are general module-sheaf facts. Their natural owners are
`Aglib.AlgebraicGeometry.Modules.Linear` and the [Invertible](../../Modules/Invertible/README.md)
family; they sit here because this family is their first consumer.

[Rigidified](Rigidified.lean), imported as `Aglib.AlgebraicGeometry.Picard.Comparison.Rigidified`,
assumes a section `o : S ⟶ X`, `ho : o ≫ p = 𝟙 S`:

- `RigidifiedPair p o ho T`: a `LineBundle (pullback p T.hom)` with an isomorphism
  `(pullback (originSection p o ho T)).obj L ≅ O_T` in `T.left.Modules` (Kleiman's `u` is its
  inverse); `RigidifiedPair.Iso` (bundle isomorphisms compatible with the rigidifications), the
  isomorphism setoid, and pullback of pairs `RigidifiedPair.map` along `f : T' ⟶ T`, through
  `pullbackComp`, `pullbackCongr` and `pullbackUnitIso`;
- `rigidifiedPicardFunctor p o ho : (Over S)ᵒᵖ ⥤ Type (u + 1)`, the isomorphism classes of pairs;
- Lemma 2.9: `RigidifiedPair.isoOfBundleIso` (pairs with isomorphic bundles are isomorphic),
  `rigidifiedClass_bijective`, `rigidifiedNormalizedIso : rigidifiedPicardFunctor p o ho ≅
  normalizedPicardFunctor p o ho ⋙ forget AddCommGrpCat` and, in Kleiman's form,
  `rigidifiedRelativeIso` onto `relativePicardFunctor p ⋙ forget AddCommGrpCat`, both sending
  `[(L, α)]` to the class of `L` (`_hom_app_mk`). Only the section is used;
- Lemma 2.10: `RigidifiedPair.Iso.eq_of_isIso_c` (with `[IsIso (pullback.snd p T.hom).c]`,
  isomorphisms of pairs over `T` are unique), `subsingleton_of_isIso_c`, `eq_refl_of_isIso_c`,
  and `eq_of_isProper_of_flat_of_geometricallyIntegral` for `S` locally Noetherian and `p`
  proper, flat, geometrically integral, from the F4 endpoint
  `isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral`.

The functor laws of `rigidifiedPicardFunctor` follow from Lemma 2.9; no coherence of the
pullback pseudofunctor is used.

[Injectivity](Injectivity.lean), imported as `Aglib.AlgebraicGeometry.Picard.Comparison.Injectivity`,
has no hypothesis on `p` except in the last item:

- `toFppfPicardSheaf_isLocallyInjective`;
- `equalizerSieve_mem_of_toFppfPicardSheaf_app_eq_zero` and
  `exists_sieve_of_toFppfPicardSheaf_app_eq_zero`: a class with zero image in
  `Pic_{X/S,(fppf)}(T)` vanishes in `Pic(X ×_S U)` for all `U ⟶ T` in an fppf covering sieve;
- `FppfLocallyTrivialMemBaseImage p`: every fppf-locally trivial class on `X ×_S T` lies in the
  image of `Pic(T)`; `fppfLocallyTrivialMemBaseImage_iff_injective` proves it equivalent to
  injectivity of `toFppfPicardSheaf p` on every `T`, and
  `mono_toFppfPicardSheaf_of_fppfLocallyTrivialMemBaseImage` gives the monomorphism;
- the module form of O-connectedness, in `Scheme.Modules`: `isIso_unit_app_unit_of_isIso_c`
  (if `q.c` is an isomorphism, the adjunction unit `O_T ⟶ q_* q^* O_T` is one, through
  `unitToPushforwardObjUnit` and `pullbackUnitIso`) and, for `S` locally Noetherian and `p`
  proper, flat, geometrically integral,
  `isIso_unit_app_unit_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral`.

## Not yet proved

- Kleiman's Thm 2.5(1): `FppfLocallyTrivialMemBaseImage p` for `S` locally Noetherian and `p`
  proper, flat, geometrically integral. Two routes are available.
  - Kleiman's argument (p. 19) needs, for `q = pullback.snd p T.hom`, quasi-coherence of
    `q_* L`, flat base change of `q_*`, the counit `q^* q_* L ⟶ L` after base change, and
    faithfully flat descent of invertibility and bijectivity (row F5). Aglib already proves
    quasi-coherence of the higher direct images of a quasi-coherent module under a qcqs
    morphism in every degree, including 0 (`moduleHigherDirectImage_isQuasicoherent`,
    `Cohomology/DirectImage/QuasiCoherent.lean`), quasi-coherence of the pushforward along a
    quasi-compact open immersion (`quasicoherent_pushforward_open`), and flat base change of
    those higher direct images for qcqs `f`, flat `j` and every `n`, including 0
    (`higherDirectImageFlatBaseChangeIso`, `Cohomology/BaseChange/HigherDirectImage.lean`).
    What is missing is at most the identification in degree 0 of
    `(pushforward q).rightDerived 0` with `q_*` (Mathlib's `rightDerivedZeroIsoSelf`)
    compatibly with these maps, and the compatibility of the counit with base change.
  - [Stacks 0B9M](https://stacks.math.columbia.edu/tag/0B9M) proves the premise without flat
    base change, from F4 and F6 inputs. Universal O-connectedness, applied to global units,
    makes the transition units of the local trivializations units on the overlaps of the base.
    Effective fppf descent of invertible sheaves gives `N` on `T`, and full faithfulness of
    descent gives `q^* N ≅ L` (Stacks 023T).
- Thm 2.5(2) (with a section the comparison map is an isomorphism), which needs the fppf stack
  property of line bundles (row F6).

## Consumers

The focused tests are `AglibTest.AlgebraicGeometry.Picard.Comparison.Endomorphisms`, `.Rigidified`
and `.Injectivity`. Planned consumers are Thm 2.5(2), the normalized representability of
target 6 and the representability assembly (F17).
