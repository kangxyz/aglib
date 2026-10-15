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
[Morphisms/Finite/PointLifts](../Morphisms/Finite/PointLifts.lean), without an
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
[Morphisms/Etale](../Morphisms/Etale/README.md). This family imports no R5Lab,
etale H1, normalization, inertia, pointed-application or K-theory layer.
The current external consumer is the R5 finite-etale foundation; its higher
Galois, descent and application modules remain downstream. The isolated
`AglibTest.FiniteEtale` client checks the canonical object/maps, empty cover,
field-only finiteness and fibre/base-change equations.
