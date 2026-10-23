# Generic and finite-presentation coefficient inputs

This family supplies generic detection, finite Galois trivialization and
finite-presentation results for actual small-etale abelian coefficients
`AbelianSheaf.{u,u+1}`. The generic-detection, normal-constant and
field-trivialization declarations use the native namespaces
`EtaleCohomology.GenericDetection`, `EtaleCohomology.NormalConstants`
and `EtaleCohomology.FieldTrivialization` under
`AlgebraicGeometry.Scheme`. The geometric finite-presentation declarations
use `AlgebraicGeometry.Scheme.EtaleCohomology.Constructible`.

## Generic restriction

Let `X : Scheme.{u}` be integral and
`j := X.fromSpecStalk (genericPoint X)`.
[GenericDetection](GenericDetection.lean) proves `mono_genericUnit`:
for every actual finite locally constant `F`, the original unit

```lean
(inverseImageAdjunction j).unit.app F
```

is a monomorphism. Its finite étale group representation is constructed from
finite local constancy. Normality and Noetherianity are not required.
The lower [represented result](GenericDetection/Represented.lean) proves
injectivity of original generic pullback on maps from étale test schemes
into separated schemes over `X`, and the corresponding original unit
for separated étale represented abelian coefficients.

[NormalConstants](NormalConstants.lean) gives the stronger finite-constant
result when every local ring of `X` is integrally closed. For finite
`A : AddCommGrpCat.{u+1}`, `isIso_genericUnit_constant` makes the
original generic unit invertible, and `constantGenericIso` retains the
original unit followed by the native inverse-image constant-sheaf comparison.
Its target is the original direct image of the constant coefficient on
`Spec X.functionField`. No Noetherian or coefficient-order premise is added.

## Finite Galois trivialization over a field

For any field `K : Type u`,
[FieldTrivialization](FieldTrivialization.lean) constructs, from
`IsFiniteLocallyConstant F`, an actual
`L : FiniteGaloisIntermediateField K (SeparableClosure K)`, a finite
`A : AddCommGrpCat.{u+1}`, and an isomorphism

```lean
(inverseImage (Spec.algebraMap K L)).obj F ≅
  (constantSheaf (Scheme.smallEtaleTopology (Spec (.of L)))
    AddCommGrpCat.{u+1}).obj A
```

`Trivialization` stores these data, and
`exists_finiteGalois_trivialization` states their existence. The theorem
requires no prescribed marking, perfection or invertibility of the coefficient
order. Points used to obtain a chart lift provide existence witnesses.

## Finite local constancy on a qcqs base

For a qcqs `X : Scheme.{u}` and an actual
`F : AbelianSheaf.{u,u+1} X` with `IsFiniteLocallyConstant F`,
[FiniteLocallyConstantCompactness](FiniteLocallyConstantCompactness.lean)
proves `isFinitelyPresentable_of_isFiniteLocallyConstant`, with conclusion
`IsFinitelyPresentable.{u+1} F`. This is ordinary finite presentability in
the abelian sheaf category, with coefficient and filtered-index universe
`u + 1`.

For a small filtered `I : Type (u + 1)`, a coefficient diagram `D`
and a supplied colimit cocone `c`, every original
`a : F ⟶ c.pt` factors as `b ≫ c.ι.app i = a` through an original
stage. If `a,b : F ⟶ D.obj i` have equal composites into `c.pt`,
there is a transition `f : i ⟶ j` with
`a ≫ D.map f = b ≫ D.map f`.

The finite étale group representation is constructed internally from finite
local constancy. Its carrier `Y` and actual binary product `Y ×_X Y`
are qcqs; the accepted original section-continuity theorem applies to both.
Morphisms out of the represented coefficient are sections on `Y`
satisfying the original group-law equation on `Y ×_X Y`, giving the
stage factorization and eventual equality above. No supplied presentation,
marking, coefficient-order invertibility or Noetherian hypothesis is required.

Existence of an explicit finite-`ZMod` generator/relation presentation
remains a separate question. Ordinary finite presentability for these finite
locally constant coefficients does not require that presentation. Finite
cogeneration and finite presentability of general constructible coefficients
remain open.

## Explicit presentations on qcqs étale objects

[FinitePresentation](FinitePresentation.lean) supplies
`qcqsEvaluation_preservesFilteredColimits` for a chosen
`U : X.Etale` whose underlying scheme is qcqs. The base `X` is
arbitrary. Both the coefficient value and filtered-index size are `u + 1`.

The existing integer free representable on `U`, its native scalar-quotient
cokernel `freeZModRepresentable X.smallEtaleTopology n U`, and finite sums
of these generators
are `IsFinitelyPresentable.{u+1}`.
For finite families `U0` and `U1` of such qcqs objects, an actual
relation arrow `d`, quotient arrow `q`, equation `d ≫ q = 0`, and
cokernel-colimit certificate give finite presentability of the presented
coefficient `F`. Every original map from `F` to a supplied filtered
colimit factors through an original stage, with equation
`b ≫ c.ι.app i = a`; the original Hom cocone is also a colimit.
These results allow every modulus, including zero and one, and empty finite
families.

The lower
[generic finite-presentation family](../../../CategoryTheory/Sites/Torsion/README.md)
owns the scalar-quotient Hom equivalence and finite-colimit argument.
Finite cogeneration and existence of these presentations for arbitrary finite
locally constant or constructible coefficients remain open.
