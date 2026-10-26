# Complexes and quasi-isomorphism comparison

[MappingCone.QuasiIso](MappingCone/QuasiIso.lean), imported as `Aglib.Algebra.Homology.MappingCone.QuasiIso`, exports `CochainComplex.quasiIso_of_mappingCone_acyclic`. For an actual integer-indexed cochain map in an arbitrary abelian category, acyclicity of its mapping cone implies that the map is a quasi-isomorphism. The category and its morphism universe are retained; no geometric exactness or derived-equivalence premise is used.

[TotalComplex](TotalComplex/README.md) supplies the first-quadrant module and abelian-group comparison, including the actual injection/augmentation maps and native signs. [CategoryTheory/Abelian/Injective](../../CategoryTheory/Abelian/Injective/README.md) owns generic resolution kernels and exact-functor Ext comparison. [Site Cech](../../CategoryTheory/Sites/SheafCohomology/Cech/README.md) and [scheme cohomology](../../AlgebraicGeometry/Cohomology/README.md) are consumers of these actual comparison results.

Latest local Quillen additions include [CochainComplexPlus](CochainComplexPlus/README.md), [actual truncation layers](Embedding/StupidTrunc/README.md), [bounded homotopy comparison](HomotopyCategory/Plus/README.md), [D+ and right-derived units](DerivedCategory/README.md), and [short-complex retract exactness](ShortComplex/README.md). [DegreewiseSplitMono](CochainComplex/DegreewiseSplitMono.lean) supplies termwise splitting and its isomorphism, zero, pushout and multiplicativity laws in the abelian setting; it does not provide a chain retraction. [KernelSequence](CochainComplex/KernelSequence.lean) constructs the actual kernel sequence of an acyclic cochain complex, and [MappingCone.Acyclicity](MappingCone/Acyclicity.lean) gives the converse cone-acyclicity result for a quasi-isomorphism. [SingleShift](CochainComplex/SingleShift.lean) retains the original shifted-single normalization.

The [cochain-complex guide](CochainComplex/README.md) records the kernel, splitting and single-shift conditions. The [mapping-cone guide](MappingCone/README.md) adds the generic additive identity-cone functor and its pushout and short-exactness comparisons. [QuasiIso](QuasiIso.lean), imported as `Aglib.Algebra.Homology.QuasiIso`, proves `CochainComplex.quasiIso_of_two_acyclic`: any actual map between two acyclic integer cochain complexes in an abelian category is a quasi-isomorphism. Both acyclicity proofs are explicit inputs.

[RightDerived/Represented](RightDerived/Represented.lean) compares original
Ext with the native natural-degree right derivatives of the additive
represented functor, retaining coefficient naturality and the original
degree-zero unit. It keeps the displayed Ext universe and enough-injectives
assumption. [RightDerived/Postcomp](RightDerived/Postcomp.lean) owns the
additive postcomposition constructors and original comparison values used by
the [site module-cohomology family](../../CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/README.md).

[Semicontinuity](Semicontinuity.lean) proves upper semicontinuity of the
homology dimension of the original residue-field scalar-extension complex,
for any complex shape. In degree `i`, only finiteness of `K.X i` and finite
presentation and flatness of `K.X (c.next i)` are required. The finite-projective
specialization needs neither boundedness nor Noetherianity. The proof uses
the original short complex and its cokernels, without assuming that homology
commutes with tensor product.

[EulerCharacteristic](EulerCharacteristic.lean) proves the native
Euler–Poincare identity for a termwise bounded complex of finite-dimensional
vector spaces. Its bounded-support result works over a nontrivial ring
without requiring finite terms.
The [fibre Euler-characteristic guide](EulerCharacteristic/README.md) records
local constancy for the actual residue-field complexes of bounded finitely
presented flat complexes. These numerical results are lower prerequisites;
a geometric application must still identify the original fibre cohomology
with that of the displayed complex.

[Koszul](Koszul/README.md) constructs finite native tensor Koszul complexes,
their original signed differential and actual quotient augmentation, and the
regular-sequence projective resolution. Its generic proofs are selected from
the supplied Motivic library; geometric purity remains a separate consumer.

[ModuleCat](ModuleCat/README.md) and
[MultiplicationCone](MultiplicationCone/README.md) document finite module
homology and the actual multiplication-cone quotient/transport maps. Their
finite-length and scalar regularity conditions remain explicit.
