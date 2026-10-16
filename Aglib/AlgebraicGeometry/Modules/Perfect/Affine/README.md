# Native affine strict perfect models

This is the unique affine helper family. The core predicates and model
category come from the canonical [PerfectComplexes](../../PerfectComplexes/README.md)
family, reexported by the legacy core paths for compatibility. No affine
tilde/model counterpart exists in that canonical core, so these actual
helper implementations remain here. Their native mathematical namespace
is `Scheme.Modules.Complex`; no second strict-perfect predicate, derived
restriction functor or globally registered derived-category instance is
introduced.

Import `Aglib.AlgebraicGeometry.Modules.Perfect.Affine`.
`Scheme.Modules.Complex.strictPerfect_tilde_of_finite_projective R P a b`
proves strict perfectness of the actual complex obtained by applying the
native `tilde.functor R` termwise to `P`. It assumes strict native term
bounds `a,b`, and finite projective original modules in each degree.
The resulting sheaf complex has the same term bounds. Each original tilde
term is finite locally free by the actual affine local-basis theorem.

The ring is arbitrary and need not be Noetherian. The theorem neither
replaces the complex nor infers term bounds from homology bounds. It does
not by itself identify this strict perfect complex with a derived direct
image. That endpoint additionally needs an actual derived-object comparison
to the installed derived pushforward.

The leaf passed alone through the shared guarded wrapper with receipt
`1792103333225003000-42485`. Its immediate projective consumer applies it
to the constructed bounded finite-projective cohomology model, before
assembling the original affine counit and derived-pushforward comparisons.
The external `AffineStrictPerfectModelConsumer.lean` passed with receipt
`1792103912938134000-54284`. It applies the theorem to the actual constructed
projective-model complex over an arbitrary native commutative ring object
in universe `u`, with no Noetherian premise on that comparison. The strict
perfectness theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

`Affine.Model` owns the unique actual `tildeModelMap R P K q`: native tilde
of the actual module map `q : P → Γ(K)`, followed by the original native
tilde/global-sections counit. Its component formula, quasi-isomorphism
composition criterion and `hasStrictModel_of_tildeModelMap` use these same
original arrows. The ambient target `K` has no term-bound hypothesis.
Boundedness and finite projective terms are required of the source `P`
when constructing the native strict-model witness.

`tildeModelMapPlus` and `tildeModelDerivedIsoPlus` separately require actual
native bounded-below packings `P` and `K`. Their forward map is the literal
localization of the original map. There are no higher-cohomology imports,
Noetherian hypotheses or assumed endpoint comparison families. Geometric
consumers supply actual proved section-model and original-counit
quasi-isomorphisms. This sole lower implementation passed with receipt
`1792106108684125000-94026`; the projective sheaf names became thin
delegations and passed with receipt `1792106203508648000-95466`.
The independent `AffineStrictModelMapConsumer.lean` passed with receipt
`1792106416102153000-98257`, checking the actual map and native strict-model
witness for an arbitrary ambient target complex. Its inspected declarations
use only the three standard axioms. The refreshed projective sheaf consumer
passed with receipt `1792106419136475000-98324`, retaining the same original
section comparison and counit through the lower delegation.

The bounded owner reconciliation with current `main` keeps both affine
mathematical bodies byte-identical. `Affine` now imports the canonical
strict-perfect leaf directly, and `Affine/Model` retains the old model
import's transparent compatibility surface. The old local standard and
derived-restriction names are abbreviations of the same canonical values.
Actual source and target complexes, the literal `fromTildeΓ` component,
quasi-isomorphism conditions, term bounds and native localized forward
maps remain unchanged.

The isolated current-main owner reconciliation compiled unique `Affine`
with receipt `1792129954444191000-27061` and unique `Affine/Model` with
`1792130030739867000-27874`. The combined native old/canonical consumer
passed `1792131484008393000-41087`, including the literal original
`tilde.map (q.f j) ≫ fromTildeΓ` component and a strict-model witness for
an arbitrary ambient target complex. Its seven inspected declarations use
only the three standard axioms. Canonical core source files and both
unique affine mathematical bodies remain unchanged.
