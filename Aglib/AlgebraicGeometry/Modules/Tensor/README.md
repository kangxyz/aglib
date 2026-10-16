# Canonical scheme module tensors

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.Tensor.Basic`, defines `AlgebraicGeometry.Scheme.Modules.moduleTensorLeftFunctor`, `moduleTensorRightFunctor` and `moduleTensorCoefficientMap` on actual scheme modules. They specialize the single [site tensor construction](../../../Algebra/Category/ModuleCat/Sheaf/Tensor/README.md). The coefficient map has the original identity/composition and component formulas; the right functor is defined in this same lower leaf.

[Restriction](Restriction.lean), [Sheafification](Sheafification.lean), [Sections](Sections.lean) and [SectionStalk](SectionStalk.lean) compare actual open restriction, associated sheaves, sections and germs with this tensor. [Symmetry](Symmetry.lean) supplies the native braiding and left/right comparison without importing projection formula or invertible sheaves. [Stalk](Stalk/README.md) fixes the actual scalar tensor and pure-germ formulas.

A supplied retract of finite free coefficients gives the stated pulled-back tensor short-exact result in Basic. General finite-locally-free left/right exactness and `PreservesHomology` belong to [LocallyFree/Tensor/Exact](../LocallyFree/Tensor/README.md). Tensor construction alone does not assert arbitrary-coefficient exactness.

Projection formula, Godement tensor and [ordinary Picard tensor](../Invertible/README.md) are consumers of these same objects/maps. The higher `TensorComparison` explicitly relates the invertible wrappers to the canonical tensor.

[Linear](Linear.lean) proves structural linearity of the original
`moduleTensorLeftFunctor` for every explicit ring map into global functions.
`moduleTensorLeftFunctor_map_globalScalarEndomorphism` retains the actual
scalar-center endomorphism, and `moduleTensorLeftFunctor_map_smul` applies
to arbitrary coefficient morphisms. The proof uses the original
pure-tensor section generators and sheafification unit. The structural
ring and scheme universes are independent; no QC, flatness or finiteness
is required. The source passed `1792124172271151000-66462`; the raw
independent-universe and opposite-twist consumer passed
`1792124277369972000-67924`, with the three standard axioms.
