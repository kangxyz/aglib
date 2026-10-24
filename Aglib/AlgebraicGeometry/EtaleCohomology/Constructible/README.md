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
`X`, without a qcqs or cohomology premise.
On qcqs `X`, [Bounded](TorsionColimit/Bounded.lean) additionally proves
`exists_positive_annihilator_of_isConstructible`: there is `n > 0`
with the original equation `n • 𝟙 F = 0`. The bound is constructed,
rather than assumed.

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
locally constant coefficients does not require that presentation. Nonaffine general
constructible finite cogeneration and arbitrary constructible finite
presentability remain separate.

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

## Bounded presentations and stratum maps

[BoundedPresentation](TorsionColimit/BoundedPresentation.lean) works on any
scheme with an actual equation `n • 𝟙 F = 0`, for every natural `n`,
including zero and one. `exists_filtered_presentation` constructs a small
filtered `I : Type (u+1)`, a diagram in the full category of n-killed
coefficients and an actual colimit cocone with point `F`. Its stages are
finite colimits of the original affine free mod-n representables. For positive moduli,
their geometric constructibility is supplied below on separated schemes.

[Strata](FiniteCogenerators/Strata.lean) proves joint faithfulness of original
inverse images along covering immersions. Given an actual
`FiniteLocallyClosedPartition X`, original stratum monomorphisms give
`mono_adjunctionProduct` into the finite product of direct images;
each coordinate is the original unit followed by the direct image of the
supplied stratum map. `mono_unitProduct` specializes to the original
restriction units. This does not construct a global disjoint partition from
the qcqs finite cover.

[AffineIntegralConstants/Sections](FiniteCogenerators/AffineIntegralConstants/Sections.lean)
proves an actual represented finite-constant section-cocone colimit along
finitely generated subalgebras of a ring algebra `R → A`, after base
change to a fixed qcqs test `U → Spec R`. Its cocone maps are original
scheme precomposition. When `A` is integral over `R`, the stages
are finite over `R`. The section result itself does not require
integrality. [RepresentedSections](FiniteCogenerators/AffineIntegralConstants/RepresentedSections.lean)
identifies the original direct-image sections and transition maps, with their
original adjunction units. [SheafColimit](FiniteCogenerators/AffineIntegralConstants/SheafColimit.lean)
then proves the literal constant direct-image sheaf cocone is a colimit at
value size `u+1`, for arbitrary ring algebras and finite abelian values.
Integrality is needed only to make the stages finite over the base. This
does not assert arbitrary varying-system cohomological continuity.

## Completed positive-presentation suppliers

[Ambient](PositivePresentation/Ambient.lean) proves ambient finite
presentability for every original bounded-producer stage on every scheme and
for every modulus, including zero. [ModulusOne](PositivePresentation/ModulusOne.lean)
proves these stages are constructible at modulus one. Neither result infers
geometric constructibility from finite presentability for other moduli.

[Partitions](FiniteColimits/Partitions.lean) constructs actual common finite
locally closed refinements, including empty families.
[Values](FiniteColimits/Values.lean) proves finiteness of the actual abelian
colimit of finite values when the object family is finite; the arrow family
need not be finite. [LocalTrivialization](FiniteColimits/LocalTrivialization.lean)
constructs a common actual etale chart for finitely many FLC objects. Arrow
compatibility on that chart is supplied for finite arrow families below.

[FreeSet](PositivePresentation/FreeSet.lean) proves finite local constancy of
the original free-mod-n generators for finite etale test objects when `n != 0`.
Its extension to arbitrary qc etale test objects retains a locally Artinian,
quasi-separated base. [FiniteColimits/Artinian](FiniteColimits/Artinian.lean)
supplies the actual arrow-compatible diagrams and finite-object colimit closure
on locally Artinian bases. [PositivePresentation/Artinian](PositivePresentation/Artinian.lean)
therefore gives constructible, ambient finitely presentable original stages
for nonzero moduli on locally Artinian quasi-separated bases; base
quasi-compactness is not an extra premise.

[RepresentablePullback](PositivePresentation/RepresentablePullback.lean)
identifies original free-mod-n generators under arbitrary inverse image,
for every modulus. Its constructibility consequence requires actual finite
etale structural maps on supplied finite locally closed partitions; the geometric
partitions for affine structural maps and separated-base affine generators
are constructed by the finite-stratification suppliers below.

## General finite-diagram closure

[ConstantRestriction](FiniteColimits/ConstantRestriction.lean) preserves the
literal original constant-presheaf unit under actual etale restriction.
[LocalMaps](FiniteColimits/LocalMaps.lean) simultaneously lifts finitely many
original arrows to additive value maps on an actual chart retaining a point.
The source values are finite; target values need not be finite.

[General](FiniteColimits/General.lean) uses these original arrow maps and their
proved functor laws to identify the whole restricted diagram with an actual
finite-value diagram. For `Finite (Arrow J)`, the original colimit of FLC or
constructible coefficients is FLC or constructible on every scheme. No
Noetherian, locally Artinian, compactness or separatedness premise is added.
The older Artinian result retains its weaker finite-object-only shape bound.

[FiniteEtalePartitions](PositivePresentation/FiniteEtalePartitions.lean)
therefore makes the original positive-modulus presentation stages constructible
and ambient finitely presentable from actual finite-etale partitions of the
original generators. The original diagram, cocone and index/value size `u+1`
are retained. The finite-stratification suppliers below construct this exact input on
separated bases.

## Genuine presentations and geometric strata

[GenuineModules](PositivePresentation/GenuineModules.lean) identifies the
original bounded-coefficient category with genuine ZMod sheaves through an
actual equivalence, for every modulus including zero. The original underlying
functor preserves colimits of size `u+1`. The original filtered presentation
lifts to the supplied genuine module itself; its literal underlying cocone
legs and whole cocone are recovered through the native scalar comparison.

[AffineRestriction](PositivePresentation/AffineRestriction.lean) proves ambient
finite presentability after restriction to every original affine open for
these actual stages on separated schemes. This is a theorem about the stage
closure, not arbitrary preservation of FP objects by inverse image.

[NoetherianAffine](FiniteStratification/NoetherianAffine.lean) constructs actual
finite partitions for affine locally quasi-finite finite-type maps over a
Noetherian base. [AffineEtale](FiniteStratification/AffineEtale.lean) descends an
actual etale algebra to a finitely generated integer subalgebra and pulls
back its Noetherian partition. Thus affine etale maps over arbitrary affine
bases have finite literal stratum projections.
[AffineRepresentable](FiniteStratification/AffineRepresentable.lean) supplies
the exact partition input for affine structural maps on any scheme and for
original affine-source generators on separated schemes. Together with the
positive genuine producer, it gives constructible, ambient-FP stages and
both actual colimit cocones without a Noetherian assumption. Geometric
constructibility still requires nonzero modulus.

## Finite cogenerators on an affine Noetherian base

[Affine](FiniteCogenerators/Affine.lean) constructs
`finiteConstantProductEmbeddingOfIsAffine X F hF` for an affine Noetherian
scheme, a geometrically constructible original abelian coefficient and its
explicit ambient finite-presentability instance. The result stores actual
finite source schemes over X, finite abelian values and the literal original
monomorphism into their finite constant direct-image product.

[IntegralStrata](FiniteCogenerators/IntegralStrata.lean) uses actual reduced
integral components and original generic detection.
[GenericTrivialization](FiniteCogenerators/GenericTrivialization.lean),
[GenericExtension](FiniteCogenerators/GenericExtension.lean) and
[NormalGenericModel](FiniteCogenerators/NormalGenericModel.lean) construct and
compare the original finite Galois values, normal models and generic triangles.
The integral closure may be infinite.
[Factorization](FiniteCogenerators/AffineIntegralConstants/Factorization.lean)
uses the original sheaf colimit and ambient finite presentability to select
actual finite subalgebra stages. [Spectrum](FiniteCogenerators/Spectrum.lean)
assembles their literal product map and proves its monicity.
No Japanese, Nagata or finite-normalization premise is used.

The source coefficient still needs ambient FP. Nonaffine global finite
cogeneration is separate, and arbitrary finite output groups have no prescribed
annihilator. The genuine-module annihilator adapter is supplied in
[Proper/Local](../Proper/README.md).

## Remaining geometric inputs

Global finite cogeneration on nonaffine schemes and arbitrary constructible
finite presentability remain separate obligations. The affine embedding
requires ambient FP; the actual positive presentations provide that condition
for their stages on separated schemes. General nonseparated qcqs generator
stratification is not asserted. The locally Artinian theorem retains its own
weaker diagram-shape conditions and is not the sole available geometric case.

## Constant-ring module coefficients

The [module family](Modules/README.md) uses the actual module-valued sheaf
category over a commutative ring in its independent scalar universe. Local
values are finite modules, with no finite additive-cardinality premise.
Arbitrary pullback, Zariski and jointly surjective etale descent, and
finite-etale image constructibility are supplied. Finite sums/products work
over arbitrary commutative rings; kernel, cokernel and extension closure uses
a Noetherian coefficient ring and retains the weak-Serre scope.
General finite-image constructibility, arbitrary qcqs-surjective descent and
Noetherian-model descent of coefficient objects/arrows remain separate results.
