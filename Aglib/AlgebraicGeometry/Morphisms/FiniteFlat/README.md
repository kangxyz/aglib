# Finite locally free rank and finite-scheme degree

The declarations use native scheme morphisms and their actual direct-image
structure modules. `Basic.lean` retains the incoming finite-local-basis and
constant-rank predicates; `Modules/LocallyFree/FiniteFlat.lean` supplies the
finite-flat, locally finitely presented direct-image theorem on arbitrary
bases. `Fibres.lean` and `GeometricDegreeRank.lean` compare those bases with
actual geometric fibre algebras. Algebra rank is compared with point count
only under the stated etale hypotheses.

`Degree.lean` uses the structural algebra on actual global sections of a
finite field scheme. `AffineDegree.lean`, `DegreeLength.lean` and
`DegreeIso.lean` preserve its algebra, residue-weighted lengths and actual
isomorphism comparisons. Nonreduced finite schemes retain their nilpotent
lengths. `RankOne.lean` proves the rank-one algebra/scheme isomorphism result.

`FunctionField.lean` retains the explicit finite-dominant generic-fibre and
function-field inputs. The generic lift itself and its isomorphism theorem
are the native `Scheme.genericFibreMap` and `genericFibreMap_isIso` in
`FunctionField/GenericFiber.lean`; they are not reimplemented here.

The ordinary curve finite-Cartier degree supplier is migrated separately in
`Curves/Abel/FiniteCartierDegree.lean`. Its full product-formula and actual
invertible kernel-ideal hypotheses remain explicit. Incoming theorem-family
predicates are statements, and are not witnesses merely by being defined.

Source: R5 packet revision `f8a3314ddecffcada2ec721d26d56a937bed9690`,
`R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteFlat`.
