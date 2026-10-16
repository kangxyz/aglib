# Compatibility imports and affine perfect-model helpers

The canonical core family is
[Modules/PerfectComplexes](../PerfectComplexes/README.md). The legacy
`Aglib.AlgebraicGeometry.Modules.Perfect` import paths reexport that same
implementation. There is one native `IsBounded`, `strictPerfect`,
`StrictPerfect`, `locallyPerfect`, `Perfect` and `HasStrictModel`; these
wrappers define no second predicates, categories or localization functors.
The declarations retain namespace
`AlgebraicGeometry.Scheme.Modules.Complex` and their original mathematical
hypotheses, objects and maps.

The corresponding canonical leaves are:

| Legacy leaf | Sole mathematical owner |
| --- | --- |
| `Strict` | [PerfectComplexes/Strict](../PerfectComplexes/Strict.lean) |
| `Closure` | [PerfectComplexes/Closure](../PerfectComplexes/Closure.lean) |
| `Exact` | [PerfectComplexes/Exact](../PerfectComplexes/Exact.lean) |
| `Restriction` | [PerfectComplexes/Restriction](../PerfectComplexes/Restriction.lean) |
| `Local` | [PerfectComplexes/Local](../PerfectComplexes/Local.lean) |
| `LocalRestriction` | [PerfectComplexes/LocalRestriction](../PerfectComplexes/LocalRestriction.lean) |
| `LocalModels` | [PerfectComplexes/LocalModels](../PerfectComplexes/LocalModels.lean) |
| `Homology` | [PerfectComplexes/Homology](../PerfectComplexes/Homology.lean) |

`Strict`, `Closure`, `Exact` and `Restriction` had identical source bodies
after import-owner normalization. `Local`, `LocalModels` and `Homology`
use the same native derived category, now selected by the lower shared
`Scheme.Modules.standardHasDerivedCategory` in
[DerivedCategory/Basic](../DerivedCategory/Basic.lean). Its value remains
`HasDerivedCategory.standard _`, with morphism universe `u+1` for a
scheme in universe `u`. The old `Complex.standardDerived` is a transparent
compatibility abbreviation, without a second globally registered instance.

Native exact derived restriction and its localization factorization now
belong to [DerivedCategory/Restriction](../DerivedCategory/Restriction.lean)
in namespace `Scheme.Modules`. Legacy `Complex.derivedRestrict`,
`Complex.derivedRestrictFactors`, `Complex.derivedRestrictCommShift` and
`Complex.derivedRestrict_isTriangulated` transparently delegate to those
same native values. The two former instance names are retained as values;
instance synthesis uses the single canonical registration. Ordinary
`Complex.restrict_congr`, `Complex.restrictCompIso` and
`Complex.restrictDerivedIso` retain their existing native names in the
lower owners. Legacy `LocalModels` and `Homology` also import the required
legacy dependency so old clients retain these names transitively.

Strict boundedness concerns terms of the original integer cochain complex.
Local perfectness allows a strict model and neighborhood varying with the
point; `Perfect` remains a full category of actual chain complexes and
chain maps. `HasStrictModel` is a global strict representative in the
actual native quasi-isomorphism localization. None of these predicates is
replaced by the newer canonical derived-object property
`Scheme.Modules.perfectDerivedObjects`. Homology quasicoherence and local
homology bounds remain valid without a global strict model or termwise
quasicoherence; a global homology bound still retains compactness.

[Affine](Affine.lean) and [Affine/Model](Affine/Model.lean) have no canonical
counterparts in `PerfectComplexes`. They remain the unique native owners
of `strictPerfect_tilde_of_finite_projective` and the actual affine
`tildeModelMap` helpers. The former imports canonical strict perfectness
directly. Their mathematical bodies, actual tilde/counit maps, universes,
term bounds and quasi-isomorphism hypotheses are unchanged. The ambient
target of a global strict-model witness needs no term bound; the separate
bounded-below comparison retains an actual supplied target packing. See
the [affine guide](Affine/README.md). No cohomology-only replacement or
assumed geometric comparison family is introduced.

The isolated owner reconciliation compiled each legacy leaf through the
shared one-frontend guard, with no aggregate build:

| Leaf | Integration source receipt |
| --- | --- |
| `Strict` | `1792128948775395000-13953` |
| `Closure` | `1792129068001518000-15444` |
| `Exact` | `1792129129116905000-16102` |
| `Restriction` | `1792129232242584000-17113` |
| `Local` | `1792129382638407000-18534` |
| `LocalRestriction` | `1792129560472547000-20377` |
| `LocalModels` | `1792129643132925000-21359` |
| `Homology` | `1792129793074781000-23889` |
| unique `Affine` | `1792129954444191000-27061` |
| unique `Affine/Model` | `1792130030739867000-27874` |

The independent `PerfectOwnerIntegrationConsumer.lean` passed with receipt
`1792131484008393000-41087`. It imports old and canonical owners together,
checks literal equality of the standard choice, derived functor,
factorization and shift data, checks canonical instance synthesis and the
original local-perfect/global-model formulas, and applies the actual affine
model map with no ambient target term bound. Its seven inspected
mathematical declarations use only `propext`, `Classical.choice` and
`Quot.sound`. Canonical source hashes and the two unique affine
mathematical bodies were checked unchanged.
