# Admitted étale cohomology foundations — 2026-10-23

This source admission starts from Aglib integration base
`072fdf05bbe3d22eb0b943c71a9cbc7c3849ac17`, from upstream baseline
`c6f64b5b133624fae3ad8650f456194180be7ba2`, with Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

| Delivery | Source identity and admitted boundary | Current owner / consumer |
| --- | --- | --- |
| A — generic site and module cohomology | Archive `aglib-site-cohomology-source-20261023T004143Z.tar.xz`, SHA-256 `3359438fa613cfc8244a6a18fab90a3bbf2c854ac83d84bd5a2bd09e31baf1d7`. Sixty-eight completed production leaves, including the shared Ext-zero provider and original affine consumer edit. | [Site cohomology](../../Aglib/CategoryTheory/Sites/SheafCohomology/README.md); concrete consumers are its `Slice/Etale` and `ModuleCoefficients/Etale` entries. |
| B — bounded-below derived and étale comparisons | Archive `etale-coherence-source-20261023T001637Z.tar.gz`, SHA-256 `c99048f0975ff040b22f043017bd17b75d364d9ec5b793183ea43887575895b4`. Fifty-three completed production leaves. | [Right-derived comparisons](../../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/README.md) and [étale cohomology](../../Aglib/AlgebraicGeometry/EtaleCohomology/README.md). |
| C — H¹ continuation | Archive `etale-coherence-source-20261023T013516Z.tar.gz`, SHA-256 `f77d1fbd50a641d5a37f4701cc7284d463137daa9db941a1d59af1849dc43a12`. Eight selected deltas: five new leaves and three replacements. | [Étale cohomology](../../Aglib/AlgebraicGeometry/EtaleCohomology/README.md), on the selected `Derived/BaseChange` version. |
| Principal mainline — Frobenius difference | [FrobeniusDifference](../../Aglib/LinearAlgebra/FrobeniusDifference.lean), SHA-256 `098313150a1c1b5e3e27046693ab5cd0b7588fdba5ad1359975ab953a8bb2eb6`. | The `LinearMap` finite-dimensional semilinear difference result, documented below. |

## Scope supplied by A

The actual slice restriction has an exact left adjoint built from hom-indexed
coproducts and sheafification. The free-representable Ext comparison identifies
with literal slice `Sheaf.H`; the original maps, coefficient and restriction
naturality, degree-zero evaluation, and Mathlib `H'` comparison are retained.
The small-etale entry uses scheme universe `u`, abelian coefficient values
`u+1`, and Ext universe `u+2`.

For module coefficients, actual injective module sheaves are acyclic for
underlying original abelian cohomology without assuming scalar-forgetting
preserves injectives. Module Ext compares with original abelian `Sheaf.H`, and
actual module evaluation `rightDerived` uses `restrictScalars` for
coefficient-valued sections. The constant-ring action comes from the
constant-sheaf adjunction unit; no identification of the constant ring with
all global sections is asserted. The Gamma long exact sequence is additive,
with its boundary normalized through the canonical original Ext class. No
separately preselected native right-derived boundary or module-linear LES claim
is made.

## Scope supplied by B

The admitted leaves supply original all-degree étale cohomology pullback and the
canonical bounded-below `D+`/global-sections comparison, including the native
`D+` adjunction and composition data, canonical mate and higher maps, and the
actual degree-zero ordinary normalization. This is not closure of the concrete
`H1` exchange or the full ordinary/derived/all-degree pasting. Proper base
change and unbounded derived claims remain outside scope.

## Scope supplied by C and the mainline result

The selected H¹ continuation adds [ActualPasting](../../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/ActualPasting.lean), [CoherenceDiagram](../../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/CoherenceDiagram.lean), [CoherenceNormalization](../../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/CoherenceNormalization.lean), [CoherenceRawNormalization](../../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/CoherenceRawNormalization.lean), and [HigherHorizontalEdges](../../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/HigherHorizontalEdges.lean), and selects replacement versions of `H1Normalization`, `HomAction`, and [Derived/BaseChange](../../Aglib/AlgebraicGeometry/EtaleCohomology/Derived/BaseChange.lean). The older accepted [BaseChangeMap](../../Aglib/AlgebraicGeometry/EtaleCohomology/BaseChangeMap.lean) is retained. For `CoherenceDiagram`, the selected source is the accepted graph087 backup; its uncompiled current raw archive version is excluded. The current raw `Aglib/AlgebraicGeometry/EtaleCohomology/BaseChangeMap.lean` archive draft is likewise excluded.

Under the source's `HasExt` hypotheses on both abelian-sheaf categories, `derivedBaseChangeMap_h1_normalized` identifies the actual canonical mate action on an original `H1Etale` representative with the original `h1Pullback` after the stated constant-sheaf, adjunction, shift, and single comparisons. This does not prove the original H¹ pullback-square compatibility or identify sections of `R¹` with fibre `H¹`. Full ordinary/derived/all-degree pasting remains open. Independent ordinary review accepted all eight selected continuation sources, and the fresh principal-owned integration compilation passed.

[LinearMap.surjective_sub_id_of_frobenius](../../Aglib/LinearAlgebra/FrobeniusDifference.lean) proves surjectivity of `v ↦ F v - v` for a finite-dimensional vector space over a separably closed field of characteristic `p`, for any Frobenius-semilinear `F`; no perfectness or invertibility premise is required. Its existing ordinary proof review is retained. The author header and public tactic import were normalized to the native production policy; the mathematical proof is unchanged and the final integration checks cover that source.

## Integration boundary and evidence

The current manifest contains 127 production source paths: A's 68, B's 53, five new H¹-continuation paths and the Frobenius source. C replaces three already-enrolled source versions without removing their import entries. The previously excluded `HigherHorizontalEdges` version is historical only; the selected current version is included. The uncompiled raw `BaseChangeMap` and `CoherenceDiagram` candidates remain excluded. Archive B lacked its original invocation logs; the new integration uses fresh native evidence. Package pins remain unchanged. The scope is the selected production closures, with no full-package CI or downstream-library claim.

Independent ordinary reviews accepted A1's fifteen-source slice/universe
closure, A2's fifty-three-source module/Ext/affine-consumer closure, and B's
fifty-three-source completed derived/etale claims at their delivered hashes.
Two B source files had obsolete draft comments removed; their Lean tokens
outside comments are unchanged. The duplicate
`CategoryTheory.InjectiveResolution.extMk_ι_zero` and its private helper were
removed from `ExtRightDerived`; its public import now uses the canonical lower
`CategoryTheory/Abelian/Injective/ExtZero` provider. The public statement and
consumer maps are unchanged, and bounded independent reconciliation retains
the prior source acceptance. The two duplicated extension-comparison naturality
lemmas likewise use their existing lower
[MapExtend/Naturality](../../Aglib/Algebra/Homology/Embedding/MapExtend/Naturality.lean)
owner; the unchanged consumer now supplies its explicit functor arguments.
Bounded independent reconciliation retained both canonicalizations. The two
mate-identity theorems remain explicit rewrite rules under Mathlib's existing
simp normal form. The shared middle-functor hypothesis of the associativity
family is retained with a documented declaration-local unused-argument annotation.
The selected coherence diagram also received field documentation only.

The eight-source H¹ extension has a separate accepted ordinary review. Its
remaining source pullback-square and full scheme-pasting boundaries above are
not additional premises of the accepted normalized-mate theorem. These are
source-adoption verdicts, not exposé-status assignments.

The final successful native run is
`remote-72bef84945594660b67017b796d13fdc`, on source digest
`404c9780b495c969776dd540e241bebedc109ce21b70765e3f76bed02b1b97e4`.
It builds the 127 selected sources together with the actual henselian Picard
consumer, preserves the previous generated-entry/text-style successes, and
passes the repaired origins with all fifteen native declaration linters.
The other twelve origin-prefix successes are retained from
`remote-cd2d8a0812f34300b874ab416304fd92`. The pinned upstream production axiom
auditor reports 4,748 audited Aglib declarations, no violations, and only
`propext`, `Classical.choice`, and `Quot.sound`. Source guards passed on the
4,691-module production layout after enrollment and import-policy repair;
subsequent changes are documentation and declaration-local lint annotations.
`AglibTest` and downstream packages are outside the requested validation scope.

[Performance findings](../PERFORMANCE.md) retain the completed comparison
repair records from both deliveries alongside the existing Picard and
upstream findings, with historical observations identified as author reports.
