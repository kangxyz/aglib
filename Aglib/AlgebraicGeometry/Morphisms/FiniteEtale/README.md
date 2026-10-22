# Finite etale schemes over a scheme

[Basic](Basic.lean) defines `AlgebraicGeometry.Scheme.FiniteEtale X` as the actual full
subcategory of `Over X` selected by `Scheme.finiteEtaleProperty`: the structural
morphism is finite and etale. Morphisms are all morphisms over `X`. Surjectivity
is not an object condition; empty covers are included. This is the one native
implementation, with methods in `Scheme.FiniteEtale`.

`mk` constructs an object from an actual finite etale scheme map. `forget` is
the fully faithful inclusion into `Over X`; `forgetToScheme` retains the
original source scheme and underlying morphism. `toEtale` maps fully faithfully
into Mathlib's existing `X.Etale`; `toEtaleForgetIso` identifies its composite
with the actual inclusion into `Over X`.

[Fiber](Fiber.lean) defines `Fiber x Y` as `Over.mk x` morphisms to `Y` and
`fiber x` by actual postcomposition. It supplies `fiberToFinite x` in Mathlib's
`FintypeCat`, with `fiberToFiniteForgetIso` identifying the original Types-valued
functor. These constructions require only a field-valued point; its field
need not be closed. The two weaker finite-morphism finiteness theorems live in
[Morphisms/Finite/PointLifts](../Finite/PointLifts.lean), without an
etale or surjectivity premise.

Under `IsSepClosed K`, `smallEtaleFiberIso` compares this same fibre with the
restriction of Mathlib's `Scheme.pointSmallEtale x`. `pointToPreimage_surjective`
states that every point in the topological fibre admits a field-valued lift.
It does not identify distinct lifts or assert injectivity. No Galois-category,
fibre-faithfulness, connectedness, cohomology or classification premise is
introduced here.

[BaseChange](BaseChange.lean) supplies `baseChange f` for every scheme map
`f : S ⟶ X`, using the actual `Over.pullback f`. Its identity and composition
isomorphisms are the canonical `Over` ones. `fiberBaseChangeEquiv` is the
map-pullback adjunction; its forward map is the actual pullback lift and its
inverse is composition with the first projection. `fiberBaseChangeIso` and
`fiberToFiniteBaseChangeIso` retain those maps naturally in the cover.

All schemes and fields retain the declared universe `u`. No Noetherian,
quasi-compact, quasi-separated, connected or nonempty-cover hypothesis is
needed by these object, finiteness and base-change results. Separably closed
fields are required only for the two geometric-point results above.

Morphism-level etale stalk and neighborhood results remain under
[Morphisms/Etale](../Etale/README.md). The object, fibre and base-change foundation imports no R5Lab,
etale H1, inertia, pointed-application or K-theory layer. The generic-restriction
leaf separately uses relative normalization.
The current external consumer is the R5 finite-etale foundation; its higher
Galois, descent and application modules remain downstream. The isolated
`AglibTest.FiniteEtale` client checks the canonical object/maps, empty cover,
field-only finiteness and fibre/base-change equations.

[GenericFiber](GenericFiber.lean) proves full faithfulness of actual generic base change on the supplied finite etale schemes over an integral scheme with integrally closed actual stalks. Its extension uses the broader [smooth-source/integral-target extension](../../FunctionField/Normalization.lean). No Noetherian or dimension hypothesis is used, and no new cover-existence claim is made. The generic finite-etale normalization construction and its separately guarded finiteness/stalk conclusions belong to [Normalization/GenericFiniteEtale](../../Normalization/GenericFiniteEtale/README.md).

GenericRestriction applies the smooth-algebra generic-connectedness theorem to
actual finite-etale covers of a normal affine domain. It proves surjectivity of
the displayed generic pointed fibre-group map and injectivity of its continuous
H1 restriction. The represented etale-H1 endpoint retains the Galois-category,
fibre-functor, Ext, Stacks03AJ/03RV, finite-coefficient and equivariant-marking
inputs. The original normalization-coefficient-specific final theorem remains
pending the separate normalization producer assemblies; it is not part of this
proved generic prefix.

Focused interface guides: [Henselian residue sections](HenselianResidue.md), [actual cover comparison, sections and deck maps](Lifting.md), and [proper schemes over complete local rings](ProperCompleteLocal.md).

[ResidueLift](ResidueLift.lean) proves that the actual residue-base-change
functor is faithful and essentially surjective over every local ring. Its
object lifts retain both projections of the original cover. The general
uniqueness theorem determines maps from a universally closed source through
a formally unramified, locally finite-type target by their residue restriction.
[HenselianEquivalence](HenselianEquivalence.lean) supplies fullness and the
actual residue-functor equivalence for every Henselian local ring, without
Noetherianity or completeness. The complete Noetherian base also has the
[adic fullness supplier](Adic/Fullness.lean).

[Proper residue comparison](ProperResidue.md) proves uniqueness and reflection
of isomorphisms on the actual closed fibre of a universally closed model over
a local ring, without flatness, Noetherianity or Henselianity.
[Proper-residue fullness](ProperResidue/Fullness.md) gives full faithfulness
for a proper flat model over a Henselian DVR.
[ProperCompleteLocal](ProperCompleteLocal.md) separately proves the actual
closed-fibre equivalence for every proper scheme over a Noetherian local ring
complete for its maximal ideal. Its forward functor is literally
`baseChange (pullback.fst f (LocalRing.residueSpecMap A))`; proper coherent
Grothendieck existence supplies object effectivity, without flatness or a
projective embedding. The complete-local hypotheses belong to this theorem. The general
henselian-local comparison is supplied separately by
[ProperHenselian](ProperHenselian/README.md).

[Nilpotent comparison](Nilpotent.md) supplies actual global Hom and object
gluing and an equivalence for the original finite-étale base-change functor
across a nilpotent closed immersion of arbitrary schemes. Nilpotence means
an actual global exponent. No Noetherianity, properness or algebraization
premise is required; this does not supply general object effectivity.

## Proper henselian local comparison and limit descent

Import `Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperHenselian.General`
for the [proper henselian comparison](ProperHenselian/README.md).
For every `R : Type u` with `[CommRing R] [HenselianLocalRing R]` and proper
`f : X ⟶ Spec (.of R)` with `X : Scheme.{u}`,
`Scheme.FiniteEtale.properHenselian_baseChange_isEquivalence f` proves that

```lean
baseChange (pullback.fst f (LocalRing.residueSpecMap R))
```

is an equivalence. `properHenselianEquivalence f` has exactly this forward
functor: `properHenselianEquivalence_functor f` is proved by `rfl`.
The endpoint imposes no Noetherian, finite-presentation, completeness,
flatness, excellence, domain or projectivity hypothesis. It constructs a
[proper finite-presentation approximation](../../Approximation/Proper/README.md)
over the original base, lifts at a stage, and uses universal essential
surjectivity on proper schemes to lift residue morphisms by their graphs.

[Descent/LimitObjects](Descent/LimitObjects.lean), imported as
`Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitObjects`, supplies
`Scheme.FiniteEtale.LimitDescent.exists_cover_of_isLimit`. For a small
cofiltered diagram of qcqs schemes with affine transitions and a specified
limit `c`, every `Y : FiniteEtale c.pt` is isomorphic to
`(baseChange (c.π.app i)).obj Yi` for an actual stage cover `Yi`.
The index, scheme and hom universes are `u`. Transition maps need not be flat,
injective on rings or surjective on schemes. The theorem is an object-descent
interface with the original projection; it is also used in the proper
henselian construction.
