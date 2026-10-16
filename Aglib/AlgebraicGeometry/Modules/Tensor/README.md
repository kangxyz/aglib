# Canonical scheme module tensors

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.Tensor.Basic`, defines `AlgebraicGeometry.Scheme.Modules.moduleTensorLeftFunctor`, `moduleTensorRightFunctor` and `moduleTensorCoefficientMap` on actual scheme modules. They specialize the single [site tensor construction](../../../Algebra/Category/ModuleCat/Sheaf/Tensor/README.md). The coefficient map has the original identity/composition and component formulas; the right functor is defined in this same lower leaf.

[Restriction](Restriction.lean), [Sheafification](Sheafification.lean), [Sections](Sections.lean) and [SectionStalk](SectionStalk.lean) compare actual open restriction, associated sheaves, sections and germs with this tensor. [Symmetry](Symmetry.lean) supplies the native braiding and left/right comparison without importing projection formula or invertible sheaves. [Stalk](Stalk/README.md) fixes the actual scalar tensor and pure-germ formulas.

[ToUnit](ToUnit.lean), imported as `Aglib.AlgebraicGeometry.Modules.Tensor.ToUnit`, defines `Scheme.Modules.tensorToUnit f` for any arrow `f : L ⟶ SheafOfModules.unit X.ringCatSheaf`. This natural transformation from `moduleTensorLeftFunctor X L` to the identity is the actual coefficient tensor map followed by the canonical left unitor. `tensorToUnit_section` sends a pure section tensor `a ⊗ m` to `f(a) • m`, with `f(a)` viewed as a section of the structure sheaf on the same open. `tensorToUnit_restrict` identifies its open restriction through the actual `tensorRestrictionIso` and `restrictUnitIso`. `tensorUnitors_eq` identifies the two unitors on the structure module, and `tensorToUnit_unit` says that the component at that module is the right unitor at `L` followed by `f`. These constructions and equations require no local-freeness or rank hypothesis.

A supplied retract of finite free coefficients gives the stated pulled-back tensor short-exact result in Basic. General finite-locally-free left/right exactness and `PreservesHomology` belong to [LocallyFree/Tensor/Exact](../LocallyFree/Tensor/README.md). Tensor construction alone does not assert arbitrary-coefficient exactness.

Projection formula, Godement tensor and [ordinary Picard tensor](../Invertible/README.md) are consumers of these same objects/maps. The higher `TensorComparison` explicitly relates the invertible wrappers to the canonical tensor. The [ordinary-complex tensor-to-unit interface](../Complex/TensorToUnit.lean) applies the same natural transformation degreewise and fixes its value on a single complex.

The non-tensor `restrictionRingHom`, its invertibility, `restrictionSheafificationIso` and original restricted-unit isomorphism criteria belong to [ordinary restriction/sheafification](../Restriction/README.md). Tensor Restriction and Sheafification import those maps; the latter retains the explicit line-trivializing-cover tensor theorem.

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

The scalar-right section theorem `moduleTensorSection_smul_right` has its
sole implementation in `Linear`. Its native scalar-first parameter order is
preserved; the stalk bilinearity leaf imports that lower theorem.

[AffineSections](AffineSections.lean), imported as
`Aglib.AlgebraicGeometry.Modules.Tensor.AffineSections`, proves that the original
`moduleTensorSectionLinear` is bijective on every affine open for arbitrary
quasicoherent factors. `moduleTensorSectionIso` is the native section-module
isomorphism with that same forward map; its pure-section formula is unchanged.
The proof consumes the canonical [quasicoherent tilde tensor comparison](../QuasiCoherent/Tensor.lean)
and the original affine chart/restriction maps. It adds no flatness, finiteness,
separatedness, or Noetherian premise and has no cohomology dependency.
