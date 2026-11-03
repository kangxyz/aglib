# Original exterior maps of Kähler differentials

[Map](Map.lean), [BaseChange](BaseChange.lean) and [Values](Values.lean)
define the exterior map and its scalar extension on compatible towers of
commutative algebras, with original wedge, tensor, identity and composition
formulas. The scalar-extension comparison is the native exterior/tensor
equivalence. Localization keeps the specified submonoid, scalar action
and actual `IsLocalization` witnesses.

[GenericKernel](GenericKernel.lean) uses the same supplied fraction field
and scalar towers to prove the original localization and kernel
containment statements, with torsion-freeness only for the target that
uses it. The ring and field universes remain independent.
[GenericRankOne](GenericRankOne.lean) computes top-form rank from the
actual differential basis. Its local bidual-line result additionally
retains regular locality, dimension at most two and finite exterior
module. Scheme raw-form and regular-pair constructions use these maps.

Present consumers include [Scalar extension of Kähler and exterior differentials](../../../Algebra/Category/ModuleCat/Differentials/README.md), [Relative forms on saturated regular-pair charts](../../../AlgebraicGeometry/Blowup/Differentials/RegularPair/README.md).
