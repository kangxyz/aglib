# Constructible and finite locally constant coefficients

This family develops actual affine-local constructibility, finite locally
constant coefficients, generic detection, finite Galois trivialization and
finite-presentation inputs on the original small-etale site, with coefficients
`AbelianSheaf.{u,u+1}`. The generic-detection, normal-constant and
field-trivialization declarations use the native namespaces
`EtaleCohomology.GenericDetection`, `EtaleCohomology.NormalConstants`
and `EtaleCohomology.FieldTrivialization` under
`AlgebraicGeometry.Scheme`. Constructibility and its geometric suppliers
use the prefix
`AlgebraicGeometry.Scheme.EtaleCohomology.Constructible`. The ordinary FLC
finite-presentability theorem lives in its parent `EtaleCohomology` namespace.

## Actual constructibility and torsion

[Basic](Basic.lean) defines `IsConstructible F` on any scheme: every affine
open admits a finite partition by actual locally closed subschemes with
constructible, pairwise disjoint images covering that open, and the original
inverse image of `F` on each part is finite locally constant. This is the
abelian-sheaf clause of [Stacks 03RW](https://stacks.math.columbia.edu/tag/03RW).
`ConstructiblePartition` retains the actual schemes, immersions and
coefficient restrictions; empty strata and the empty partition of the empty
scheme are allowed. Coefficient isomorphisms transport the same partition.
Actual FLC and finite constant coefficients give examples on every scheme.

On qcqs `X`, [Basic/FiniteCover](Basic/FiniteCover.lean) constructs
`finiteLocallyClosedCover F hF`. Its finite family has actual immersions,
constructible images covering `X`, and FLC original restrictions. The
pieces may overlap: this is a finite cover, with no global disjoint partition
asserted.

[TorsionColimit/ConstructibleTorsion](TorsionColimit/ConstructibleTorsion.lean)
proves `finite_geometricStalk_of_isConstructible` for every original
geometric point `η : Spec Ω ⟶ X`, where `Ω : Type u` is a separably
closed field. It uses actual field-point factorizations through the immersions and
the original inverse-image stalk comparison.
`isTorsion_of_isConstructible` then gives internal torsion on arbitrary
`X`, without a qcqs or cohomology premise. These results do not export
a uniform positive global annihilator.

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

## Finite constant cogenerators on a connected base

[FiniteCogenerators/LocallyConstant](FiniteCogenerators/LocallyConstant.lean)
works with `F : AbelianSheaf.{u,u+1} X`,
`hF : IsFiniteLocallyConstant F` and `ConnectedSpace X`.
`finiteEtaleTrivialization F hF` constructs a finite étale surjection
`f : Y ⟶ X`, a finite `A : AddCommGrpCat.{u+1}`, and an actual
isomorphism `e` from `(inverseImage f).obj F` to the original small-etale
constant sheaf on `Y` with value `A`.

`FiniteEtaleTrivialization.embedding` is the original map

```lean
(inverseImageAdjunction f).unit.app F ≫
  (directImage f).map e.hom
```

from `F` to the original direct image of that finite constant coefficient.
`mono_embedding` makes it monic, and
`exists_finite_constant_embedding` exports the produced cover, value and
monomorphism. No Noetherian, normality, perfectness, coefficient-order or
marking premise is added. The connected-base hypothesis is retained;
qcqs alone does not replace it or supply finitely many connected components.

The separate `mono_unit_of_finiteLocallyConstant` theorem applies on
arbitrary schemes to an actual FLC coefficient and an actual
`f : Y ⟶ X` with `Flat f` and `Surjective f`. Its conclusion
concerns the literal `(inverseImageAdjunction f).unit.app F`.

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
locally constant coefficients does not require that presentation. General
constructible finite cogeneration and finite presentability remain open.

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
Existence of these explicit presentations for arbitrary finite locally
constant or constructible coefficients remains open.

## Remaining geometric inputs

General constructible finite presentability and finite cogeneration,
constructible-stage torsion-colimit presentations, and global
integral-to-finite approximation remain open. A positive global annihilator
bound is not yet part of the available interface. The finite-cover,
individual-stalk and connected-FLC results above retain their stated ranges.
