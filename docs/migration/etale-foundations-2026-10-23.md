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
| D — higher coherence continuation | Archive `etale-coherence-source-20261023T040650Z.tar.gz`, SHA-256 `d1dff8b524200b682f4ef62b27997b4d7d9bae91f24bd8e4b8b9a3a6deea5c8b`. Eleven selected sources; three are new generic whole-diagram/normalization modules. The independent `derived_archive_review` accepted D11 and the retained native field documentation. | [Right-derived comparisons](../../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/README.md) and [étale cohomology](../../Aglib/AlgebraicGeometry/EtaleCohomology/README.md). |
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

Under the source's `HasExt` hypotheses on both abelian-sheaf categories, `derivedBaseChangeMap_h1_normalized` identifies the actual canonical mate action on an original `H1Etale` representative with the original `h1Pullback` after the stated constant-sheaf, adjunction, shift, and single comparisons. At the C snapshot, the original H¹ pullback-square equation and ordinary/derived/all-degree pasting endpoints were not yet supplied. Independent ordinary review accepted C's eight selected continuation sources and its fresh principal-owned integration compilation passed; those results are historical evidence for C, not D.

[LinearMap.surjective_sub_id_of_frobenius](../../Aglib/LinearAlgebra/FrobeniusDifference.lean) proves surjectivity of `v ↦ F v - v` for a finite-dimensional vector space over a separably closed field of characteristic `p`, for any Frobenius-semilinear `F`; no perfectness or invertibility premise is required. Its existing ordinary proof review is retained. The author header and public tactic import were normalized to the native production policy; the mathematical proof is unchanged and the final integration checks cover that source.

## Scope supplied by D

The selected D source set is based on native HEAD
`175a8ee20860f4ad7470cc3b043f618502380457`; its 11 source paths are recorded in
`coherence-final-040650/integration/candidate-manifest.json`. It restores the
original H¹ square and supplies ordinary, derived, and all-degree exchange
composition/identity equations. `derived_archive_review` accepted D11 and the
retained native field documentation. The principal-owned selected native integration checks passed.

`h1Pullback_square` proves the original H¹ pullback-square equation with its
four separate `HasExt` universes. `derivedBaseChangeMap_h1_square` identifies
the actual canonical mate with the same coefficient-transported square after
the native constant-sheaf, adjunction, shift, and single comparisons. Its
`HasExt` and `HasDerivedCategory` premises remain those displayed by the
declaration.

For the underived maps, `baseChangeMap_hComp`, `_vComp`, and `_vId` give
horizontal/vertical composition and vertical-identity equations using the
original inverse-image and direct-image comparison maps. The `D+` maps
`derivedBaseChangeMap_hComp`, `_vComp`, and `_vId` give the corresponding
equations through the native derived-image adjunctions, composition
isomorphisms, and identity units under the declared derived-category
instances.

For each degree `q`, `higherBaseChangeMap_hComp`, `_vComp`, and `_vId` express
composition/identity compatibility through the actual higher source/target
comparisons and homology of composite derived images. The vertical identity
endpoint retains its original higher-image comparison; it does not identify
positive-degree direct image of the identity with the identity functor. The
whole-pasting endpoints keep the named whiskered natural-transformation
diagrams and their canonical comparison edges.

These equations do not prove exchange-map invertibility, proper base change, or
an unbounded derived statement. Independent review of D is complete; the principal-owned selected native integration checks passed.

## Integration boundary and evidence

The pre-D manifest contained 127 production source paths: A's 68, B's 53, five new H¹-continuation paths, three C replacements, and the Frobenius source. Its successful native run and checks below are historical pre-D evidence. D selects eleven source-path changes: three new generic whole-diagram/normalization modules plus eight replacements or selected continuations to task-owned paths. The rejected raw C `BaseChangeMap` and `CoherenceDiagram` versions remain excluded; their selected D versions have independent source-review acceptance. The principal-owned selected D integration checks passed. Package pins remain unchanged; neither the pre-D run nor this update claims full-package CI or downstream-library validation.

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

The eight-source C H¹ extension has a separate accepted ordinary review; its
historical square and full-pasting gaps are recorded above as of C. The D
source-level equations have their own accepted `derived_archive_review`; that
verdict is independent of C, and the selected D native integration checks passed. These are source-adoption records, not exposé-status assignments.

The pre-D successful native run is
`remote-72bef84945594660b67017b796d13fdc`, on source digest
`404c9780b495c969776dd540e241bebedc109ce21b70765e3f76bed02b1b97e4`.
It builds the 127 selected sources together with the actual henselian Picard
consumer, preserves the previous generated-entry/text-style successes, and
passes the repaired origins with all fifteen native declaration linters.
The other twelve origin-prefix successes are retained from
`remote-cd2d8a0812f34300b874ab416304fd92`. The pinned upstream production axiom
auditor reports 4,748 audited Aglib declarations, no violations, and only
`propext`, `Classical.choice`, and `Quot.sound`. Source guards passed on the
4,691-module pre-D production layout after enrollment and import-policy repair.
These receipts do not cover the later D source set. Its independent source
review is accepted; the later D integration records appear below.
`AglibTest` and downstream packages are outside the requested validation scope.

[Performance findings](../PERFORMANCE.md) retain the completed comparison
repair records from both deliveries alongside the existing Picard and
upstream findings, with historical observations identified as author reports.


## Completed local-comparison and final-coherence integration

The combined selected source set has24 new or updated declaration modules:
D's11, seven proper-henselian finite-constant H0/H1 providers, five fibrewise-closed
point providers, and the canonical original-stalk universe comparison. The actual
H0/H1 and selected-point claims retain their own hypotheses, universes and
independent ordinary source-adoption reviews. They do not assert general PBC.

The seven-source local-comparison batch
`remote-a0a9a43331d349ccb444dd0d24a3d39e` passed generated entries, text style,
both origin-prefixes with all15 declaration linters, and the pinned upstream
22379-declaration audit, with only the three approved foundations. Its1812
pre-existing source dependencies remained unchanged through the D integration,
so this compatible coverage is retained.

The D/point batch `remote-9f13737f31154c0481c5d77d471fec74` passed incremental
compilation, repaired-file text style, all other selected declaration origins,
and the pinned1423-declaration audit with no violations and only `propext`,
`Classical.choice`, and `Quot.sound`. Its only remaining findings were missing
field docstrings in HigherHorizontalDiagram and HigherWholePasting. The doc-only
repair `remote-181dae28d6ec4960bc2213e870c5f2bf` passed their text style,
ordinary incremental build including the actual Derived/BaseChange consumer,
and both origins with all15 linters. No Lean token outside comments changed;
the prior audit and other-origin coverage are retained. Generated entries
passed in `remote-50d40160fe404f1bb83de21f1d99d224` and are unchanged by these
whitespace/docstring repairs.

Source guards passed for4735 production modules and399 positive modules in
`source-checks/run-32bf945020714b9b9224bcae462f957a`. AglibTest was not executed;
no downstream/client checks, kernel replay, blanket rebuild or additional
benchmark was added. These are selected native checks, not a claim that a new
GitHub workflow has already completed. Package pins are unchanged.
