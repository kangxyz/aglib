# Finite-etale covers of a proper scheme over a complete local ring

Import `Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperCompleteLocal`.
The declarations belong to `AlgebraicGeometry.Scheme.FiniteEtale`.

Let `A : Type u` be a commutative Noetherian local ring, complete for its
maximal ideal:

```lean
[CommRing A] [IsNoetherianRing A] [IsLocalRing A]
[IsAdicComplete (IsLocalRing.maximalIdeal A) A]
```

For an actual proper `f : X ⟶ Spec (CommRingCat.of A)` with
`X : Scheme.{u}`, put
`X₀ = pullback f (LocalRing.residueSpecMap A)` and
`i₀ = pullback.fst f (LocalRing.residueSpecMap A)`.
[ProperCompleteLocal](ProperCompleteLocal.lean) constructs

```lean
properCompleteLocalEquivalence f :
  FiniteEtale X ≌ FiniteEtale (pullback f (LocalRing.residueSpecMap A))
```

Its forward functor is the literal restriction to this categorical closed
fibre. `properCompleteLocalEquivalence_functor` states, by `rfl`,

```lean
(properCompleteLocalEquivalence f).functor =
  baseChange (pullback.fst f (LocalRing.residueSpecMap A))
```

`FiniteEtale X` is the native full subcategory of `Over X` whose structural
maps are finite and etale. All morphisms over `X` are retained; empty covers
are included. `baseChange` is the existing functor induced by actual
`Over.pullback`. The proof derives local Noetherianity of `X` from properness.
No flatness, projective embedding, positive-rank, or supplied realization
hypothesis is added.

| Declaration in [ProperCompleteLocal](ProperCompleteLocal.lean) | Interface for `baseChange i₀` |
| --- | --- |
| `properCompleteLocal_baseChange_full f` | Fullness on the actual closed fibre |
| `properCompleteLocal_baseChange_essSurj f` | Every actual closed-fibre cover is a restriction of a global cover |
| `properCompleteLocal_baseChange_isEquivalence f` | Equivalence of the original restriction functor |
| `properCompleteLocalEquivalence f` | The resulting equivalence of native finite-etale categories |
| `properCompleteLocalEquivalence_functor f` | Literal equality of its forward functor with `baseChange i₀` |

## Proof route and original comparisons

[Adic/ResidueStage](Adic/ResidueStage.lean) identifies the native first
maximal-ideal thickening with the literal residue-field pullback, keeping
the original inclusion into `X`. From a cover on that fibre,
[Adic/CoverSystem](Adic/CoverSystem.lean) constructs its nilpotent tower.
[Adic/StageBaseChange](Adic/StageBaseChange.lean) uses the existing
[nilpotent finite-etale equivalence](Nilpotent.md) at positive stages; stage
zero is the actual empty-thickening pullback. The cover and all transition
maps remain those of the constructed tower.

[Adic/CoverSystemModules](Adic/CoverSystemModules.lean) turns the tower's
actual finite direct-image structure modules into a coherent adic system.
[Adic/AlgebraStructure](Adic/AlgebraStructure.lean) retains the native
commutative algebra operations. Proper Grothendieck existence supplies
`Cohomology.properAdicAlgebraization` from
[Algebraization/Operations](../../Cohomology/GrothendieckExistence/Algebraization/Operations.lean),
with a specified completion isomorphism and every original quotient algebra
map. Its base ideal here is exactly `IsLocalRing.maximalIdeal A`.

[Adic/AlgebraizedCover](Adic/AlgebraizedCover.lean) derives etaleness of all
positive-power quotient algebras from the original finite-etale stages.
The actual local algebra criterion, original stalk/germ maps, and
[Adic/CoherentGoodOpens](Adic/CoherentGoodOpens.lean) give good affine
neighborhoods at every closed-fibre point. An open containing that fibre is
the whole proper scheme over the local base, by
[LocalBaseOpenCover](../Proper/LocalBaseOpenCover.lean).
Native gluing of the original section spectra produces the global finite-etale
cover. [Adic/AlgebraizedCoverComparison](Adic/AlgebraizedCoverComparison.lean)
compares it with each original stage, and `Adic.literalResidueCoverIso`
compares its actual closed-fibre restriction with the originally prescribed
cover. This proves essential surjectivity with the original fibre comparison.

For fullness, [Adic/CompletionFullness](Adic/CompletionFullness.lean) starts
with an actual first-stage map. Nilpotent full faithfulness lifts it to the
original towers. Coherent full faithfulness lifts its native algebra map,
and [Adic/AlgebraHomReconstruction](Adic/AlgebraHomReconstruction.lean)
recovers the actual global scheme map. The original epimorphic quotient
unit detects its prescribed first-stage restriction. Faithfulness comes from
the existing [proper residue comparison](ProperResidue.md), under the
weaker universally closed local-base hypotheses of that interface.

The [adic guide](Adic/README.md) records the lower algebraization and
reconstruction inputs. The
[proper coherent existence guide](../../Cohomology/GrothendieckExistence/Proper.md)
owns the complete-base coherent theorem; locality is an additional condition
of this finite-etale application. The present result concerns finite-etale
covers over complete Noetherian local bases. An arbitrary Henselian-base
proper comparison and full cohomological proper base change are separate
statements. Ordinary cohomology remains under
[Cohomology](../../Cohomology/README.md), and general descent under the existing
[Descent](../../Descent/README.md) owners.
