# Rank-one sheaves and the ordinary Picard group

The owner is `AlgebraicGeometry.Scheme.Modules.Invertible`. [Basic](Basic.lean) defines `IsLocallyRankOne`, actual `LineBundle` objects and their `LineBundleClass` quotient by sheaf isomorphism on every scheme. Local bases are genuine singleton-indexed generators; no field, smoothness, properness or dimension hypothesis is needed.

`tensorSheaf` is sheafification of the sectionwise module tensor. [Tensor](Tensor.lean) gives tensor line bundles, actual unit/braiding and local trivialization. [TensorAssociator](TensorAssociator.lean) gives the actual associator and class associativity. Generic [InternalHom](../InternalHom.lean) and lower restriction/sheafification comparisons precede the rank-one tier.

[Dual](Dual.lean) constructs the actual dual and evaluation isomorphism. `PicardGroup X` is the ordinary additive group on the same line-bundle classes: tensor product is addition, the trivial line bundle is zero, and duality is negation. The laws use the actual unit/braiding/associator/evaluation maps.

[Pullback](Pullback.lean) preserves actual local rank one under every scheme morphism. [PullbackTensor/Local](PullbackTensor/README.md) proves the canonical tensor comparison and gives `PullbackTensor.Local.pullbackHom f : PicardGroup Y →+ PicardGroup X`, with no extra tensor-pullback theorem-family premise.

Focused imports are `Aglib.AlgebraicGeometry.Modules.Invertible.Basic`, `.Dual` and `.PullbackTensor.Local` for objects, group and additive pullback. This is the ordinary Picard group; no Picard-scheme representability or curve-degree map is included.

The canonical tensor is now defined below schemes in [ModuleCat/Sheaf/Tensor/Basic](../../../Algebra/Category/ModuleCat/Sheaf/Tensor/Basic.lean). The invertible `tensorSheaf`, its map and braiding transparently specialize that construction; [TensorComparison](TensorComparison.lean) records the object/map/braiding comparison. [TensorFunctorAssociator](TensorFunctorAssociator.lean) retains the actual associator-functor interface. Generic symmetry imports neither the invertible nor projection-formula tier.

[Gluing](Gluing.lean) constructs an actual line bundle from a family of
scheme opens covering the whole space and actual units on their pairwise
intersections. `UnitCocycle` retains the cocycle equation under the actual
restriction maps on every common subopen. Its `sheaf` is constructed from
matching local section families, with the sheaf condition proved using the
original structure sheaf. `localIso` is the canonical chart-component
projection; `localIso_transition` proves multiplication by the original
unit. `localGeneratorsData` retains the supplied cover and singleton bases,
which prove both `IsLocallyRankOne` and the canonical `IsFiniteLocallyFree`,
hence finite presentation and quasicoherence. No field, finiteness of the
cover, Noetherianity or geometric dimension hypothesis is needed. Integer
powers of a cocycle are also constructed. The focused lower leaves are
[matching sections](Gluing/Sections.lean) and [the actual glued sheaf](Gluing/Sheaf.lean).
The immediate consumer is the projective-space twisting sheaf construction.

[Gluing/Morphisms](Gluing/Morphisms.lean) constructs actual morphisms from
the glued line module into any actual module sheaf. Original local target
sections satisfying `m_j = c_ij · m_i` under every common-open restriction
define matching sections of the existing structure-linear internal-Hom
sheaf, whose sheaf condition constructs the global morphism.
`homOfLocalSections_apply` preserves the original local scalar formula,
and `homOfLocalSections_generator` sends the canonical local generator to
the supplied target section. Neither a gluing-existence premise nor
quasicoherence, finiteness or Noetherianity is required.

[TensorFunctorAssociator/Sections](TensorFunctorAssociator/Sections.lean)
records the original left/right tensor-unit and nested pure-section
formulas. `moduleLineTensorAssociator_hom_section` and `_inv_section`
use the actual associator, its original sheafification units and the
original two-line trivialization data; the third module is arbitrary.
No new tensor, associator or compatibility assumption is introduced.
The cover and scheme universes remain independent. The source passed
`1792125344557185000-79728` at default budgets; the raw native-map
consumer passed `1792125406028387000-80022`, using the three standard axioms.
