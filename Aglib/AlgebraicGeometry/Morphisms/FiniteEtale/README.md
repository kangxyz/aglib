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

Focused interface guides: [Henselian residue sections](HenselianResidue.md), [Actual cover comparison, sections and deck maps](Lifting.md).

[ResidueLift](ResidueLift.lean) proves that the actual residue-base-change
functor is faithful and essentially surjective over every local ring. Its
object lifts retain both projections of the original cover. The general
uniqueness theorem determines maps from a universally closed source through
a formally unramified, locally finite-type target by their residue restriction.
Fullness for an arbitrary Henselian base and proper-scheme comparison remain
separate. The complete Noetherian base has the existing
[adic fullness supplier](Adic/Fullness.lean).
