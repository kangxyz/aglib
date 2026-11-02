# R4 source dictionary alignment

Question: apply the original `moduleDerivedBaseChangeMap_underlying` cube at the
same K, retaining the four module derived-category data, four auxiliary abelian
derived-category data, original exchange maps and comparisons. This is source
applicability/typing analysis, not independent review or a closure verdict.

The useful route is **original HDC binder scope, then late standard-W scope,
then explicit source category parameters for the two directly projected
underlying functors**. Late standard W alone does not control the stored result
signature of `moduleDerivedUnderlying`.

## Source/data argument

Write `C_T = ModuleSheaf T Λ`, `H_T = hasSheafifyLarge T`, and let `p_T` and `q_T`
be the generic and standard proofs of
`(Scheme.smallEtaleTopology T).WEqualsLocallyBijective AddCommGrpCat.{u+1}`.
At the observed mismatch, both abelian data have the exact common constructor

```
@SheafOfModules.instAbelian
  T.Etale (Scheme.instCategoryEtale T) (Scheme.smallEtaleTopology T)
  (constantRing T Λ) H_T p_T
```

with only the last argument changed to `q_T`. WEqualsLocallyBijective is a Prop
(pinned Mathlib `CategoryTheory/Sites/LocallyBijective.lean:105`). These two
applications are definitionally equal by proof irrelevance in that last
argument; this does not require unfolding the abelian constructor. This is a
specific equality of the same data constructor applied to proofs, **not** proof
irrelevance for arbitrary `Abelian C_T` values. `Abelian` includes Preadditive
data (`CategoryTheory/Abelian/Basic.lean:112`).

Consequently the same local HDC datum, whose domain was formed with the generic
proof, can be used at the standard-proof spelling of that domain. No new
localization datum is constructed. `HasDerivedCategory` is the chosen
`HasLocalization` data (`Algebra/Homology/DerivedCategory/Basic.lean:69–82`,
`CategoryTheory/Localization/HasLocalization.lean:54–61`); it is not a Prop.
The candidate leaves all original HDC binder declarations unchanged and never
calls `HasDerivedCategory.standard`.

The native signature split is precise:

- `Exceptional/Derived/DirectImage.lean:30–31,44–63` activates standard W before
  its module HDC binders and the inverse/direct-image and adjunction signatures.
- `Exceptional/Derived/Underlying.lean:31,36–41` activates only
  `hasSheafifyLarge`. Its original `moduleDerivedUnderlying` abbreviation has a
  result functor type whose module domain carries generic W.
- `UnderlyingBaseChange.lean:38–61` has the original generic-W module HDC
  binders, but its inferred cube source categories are standard-W module
  categories. The supplied ACTUAL type confirms this: standard W occurs, generic
  W does not.

Thus a caller's later W attribute changes fresh category/K expressions but
cannot rewrite the already stored generic-W result type of
`moduleDerivedUnderlying`. Ordinary `.obj` and `.map` infer their category
parameters from that stored type. They can reintroduce generic W even after the
attribute, as the early-W closed-goal capture also shows.

The actual raw pair makes the first such projection explicit. ACTUAL nodes
821–827 apply `Functor.obj` to source/category nodes 257/311, underlying-functor
value 740 and K 418. EXPECTED nodes 821,1152–1187 apply the same projection to
generic-W source/category nodes 1154/1182, with the same value 740 and K 418.
The second direct projection is `(moduleDerivedUnderlying Λ S').map`; its
inferred endpoints likewise introduce the generic-W S′ domain. The pointwise
formula contains only these two directly projected underlying functors.

## Exact candidate and scope

`PointwiseCubeSourceTyped.lean` is an unrun candidate based on b720. It keeps the
original variable block and literal theorem value. After that block it adds
the same local standard-W attribute. In both the formation and value statements
it replaces only the X object projection and S′ map projection by:

```lean
@Functor.obj
  (DerivedCategory.Plus (ModuleSheaf X Λ)) inferInstance
  (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) inferInstance
  (moduleDerivedUnderlying Λ X) K

@Functor.map
  (DerivedCategory.Plus (ModuleSheaf S' Λ)) inferInstance
  (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S')) inferInstance
  (moduleDerivedUnderlying Λ S') _ _
  ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)
```

These explicit projection arguments survive elaboration. A typed local `let`
for each of these two original functor values is another way to retain the
chosen domain for projection; merely adding an erased term ascription is not a
reliable substitute. No functor is rebuilt, eta-expanded, or replaced. The
candidate value is still exactly
`moduleDerivedBaseChangeMap_underlying Λ f f' g g' sq.w.symm K`.

This narrows the earlier four-underlying-functor ascription suggestion to the
two projection sites actually needed by this pointwise goal. No provider or
global instance-priority edit is proposed. If this typing is used in the proper
exchange proof, the original abelian component and its IsIso fact should use
the same explicitly typed X projection; reconstructing a bare native `.obj`
there would restore the conversion boundary. The torsion hypothesis and its
original underlying-homology theorem remain unchanged.

## Evidence boundary and next action

The source-level conversion argument establishes why the proposed spelling
preserves the same data and maps. It does not establish a heartbeat cause or
that the candidate passes elaboration/kernel checking. I ran no Lean command,
remote job, native runtime, new extractor, replay, or production mutation.
The early-W failure and raw mismatch remain evidence only on their original
inputs. The author's separate late-W metadata probe is not this candidate.

The remaining question is whether the explicit projection parameters make the
candidate's goal match the original inferred cube value cheaply in the current
environment. The author can answer it with this fixed candidate in the existing
incremental diagnostic/compiler loop. If it still fails, preserve its actual
diagnostic and compare its goal to the saved source application; do not infer
that arbitrary abelian data or derived-category transports are needed.

## Input identity

- N: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/aglib`;
  observed HEAD `54d6974ace11bf7d197aa925cb8cade86db8a24f`, foreign work preserved.
- Pinned Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612` at the supplied M path.
- UnderlyingBaseChange SHA256:
  `6a84bc472cb2a3b2841d27fdb753e907371fe633c7d0364fd288518b7a31afbf`.
- ProperBaseChange SHA256:
  `4eaeb3d9a30da1e3eab8783af8fd741e455c2b54a8e4aafcc4ada2d697c1e553`;
  no coverage gained for this unpassed production source.
- Underlying SHA256:
  `9fb8e9008ea9cc367dad723066db017d5003a6ef93937ba5adf04378750f9e12`.
- DirectImage SHA256:
  `fb7f1596b3609a308d6ff4095b4d7dd01a4ee718fd63808a86a3263c450034cb`.
- Original pointwise source: b72088c989598e3e26f361def624f8dc2bd00e8d00b7e2386e6b9ef971f4c827.
- Supplied evidence owner:
  `migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair/`,
  including `RAW_PAIR_PROJECTION.json`, ACTUAL/EXPECTED raw DAGs and
  `local-w-alignment/RETURN.md`. No extraction or invocation was relabeled.
- Candidate SHA256:
  `3c14014649010a1ec81aa8629646d13ecfaf21df738f358874e46d59782256ff`.

Only this assigned R directory was written. No mathematical-status assignment
or consumer closure follows from this return.
