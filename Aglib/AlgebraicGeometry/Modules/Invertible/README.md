# Rank-one sheaves and the ordinary Picard group

The owner is `AlgebraicGeometry.Scheme.Modules.Invertible`. [Basic](Basic.lean) defines `IsLocallyRankOne`, actual `LineBundle` objects and their `LineBundleClass` quotient by sheaf isomorphism on every scheme. Local bases are genuine singleton-indexed generators; no field, smoothness, properness or dimension hypothesis is needed.

`tensorSheaf` is sheafification of the sectionwise module tensor. [Tensor](Tensor.lean) gives tensor line bundles, actual unit/braiding and local trivialization. [TensorAssociator](TensorAssociator.lean) gives the actual associator and class associativity. Generic [InternalHom](../InternalHom.lean) and lower restriction/sheafification comparisons precede the rank-one tier.

[Dual](Dual.lean) constructs the actual dual and evaluation isomorphism. `PicardGroup X` is the ordinary additive group on the same line-bundle classes: tensor product is addition, the trivial line bundle is zero, and duality is negation. The laws use the actual unit/braiding/associator/evaluation maps.

[Pullback](Pullback.lean) preserves actual local rank one under every scheme morphism. [PullbackTensor/Local](PullbackTensor/README.md) proves the canonical tensor comparison and gives `PullbackTensor.Local.pullbackHom f : PicardGroup Y →+ PicardGroup X`, with no extra tensor-pullback theorem-family premise.

Focused imports are `Aglib.AlgebraicGeometry.Modules.Invertible.Basic`, `.Dual` and `.PullbackTensor.Local` for objects, group and additive pullback. This is the ordinary Picard group; no Picard-scheme representability or curve-degree map is included.

The canonical tensor is now defined below schemes in [ModuleCat/Sheaf/Tensor/Basic](../../../Algebra/Category/ModuleCat/Sheaf/Tensor/Basic.lean). The invertible `tensorSheaf`, its map and braiding transparently specialize that construction; [TensorComparison](TensorComparison.lean) records the object/map/braiding comparison. [TensorFunctorAssociator](TensorFunctorAssociator.lean) retains the actual associator-functor interface. Generic symmetry imports neither the invertible nor projection-formula tier.
