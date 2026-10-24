# Rank-one sheaves and the ordinary Picard group

The owner is `AlgebraicGeometry.Scheme.Modules.Invertible`. [Basic](Basic.lean) defines `IsLocallyRankOne`, actual `LineBundle` objects and their `LineBundleClass` quotient by sheaf isomorphism on every scheme. Local bases are genuine singleton-indexed generators; no field, smoothness, properness or dimension hypothesis is needed.

`tensorSheaf` is sheafification of the sectionwise module tensor. [Tensor](Tensor.lean) gives tensor line bundles, actual unit/braiding and local trivialization. [TensorAssociator](TensorAssociator.lean) gives the actual associator and class associativity. Generic [InternalHom](../InternalHom.lean) and lower restriction/sheafification comparisons precede the rank-one tier.

[Dual](Dual.lean) constructs the actual dual and evaluation isomorphism. `PicardGroup X` is the ordinary additive group on the same line-bundle classes: tensor product is addition, the trivial line bundle is zero, and duality is negation. The laws use the actual unit/braiding/associator/evaluation maps.

[Pullback](Pullback.lean) preserves actual local rank one under every scheme morphism. [PullbackTensor/Local](PullbackTensor/README.md) proves the canonical tensor comparison and gives `PullbackTensor.Local.pullbackHom f : PicardGroup Y →+ PicardGroup X`, with no extra tensor-pullback theorem-family premise.

[SquareZero](SquareZero/README.md) constructs actual affine and two-affine
line-bundle lifts across intrinsic square-zero closed immersions, with
the original geometric pullback isomorphisms. Its generic binary descent
and projective-module suppliers remain in their lower owners.

Focused imports are `Aglib.AlgebraicGeometry.Modules.Invertible.Basic`, `.Dual` and `.PullbackTensor.Local` for objects, group and additive pullback. This is the ordinary Picard group; no Picard-scheme representability or curve-degree map is included.

The canonical tensor is now defined below schemes in [ModuleCat/Sheaf/Tensor/Basic](../../../Algebra/Category/ModuleCat/Sheaf/Tensor/Basic.lean). The invertible `tensorSheaf`, its map and braiding transparently specialize that construction; [TensorComparison](TensorComparison.lean) records the object/map/braiding comparison. [TensorFunctorAssociator](TensorFunctorAssociator.lean) retains the actual associator-functor interface. Generic symmetry imports neither the invertible nor projection-formula tier.

[Trivialization](Trivialization.lean) gives section coordinates and generators in an actual unit chart, with no integral-scheme premise. [Field](Field.lean) gives actual field-spectrum triviality and singleton module bases. [Locality](Locality.lean) glues local rank one along an arbitrary open cover. [ZeroLocus](ZeroLocus/README.md) gives the pointwise fibrewise-regular line-bundle theorem through actual image-ideal zero data.

[LocalRing](LocalRing.lean), [Affine](Affine.lean) and
[ChartCocycle](ChartCocycle.lean) compare Picard groups with smaller models. If a
point of `X` has `X` as its only open neighbourhood, every line bundle is trivial;
in particular `PicardGroup (Spec R)` is a subsingleton for every commutative local
ring `R` (`nonempty_iso_unit_of_isLocalRing`). Line bundles are finite locally free
and quasicoherent on every scheme (`lineBundle_isQuasicoherent`). For an arbitrary
commutative ring `R`, global sections of a line bundle on `Spec R` form an invertible
module, `tilde` of an invertible module is locally rank one, and
`picardGroupEquivCommRingPic R : PicardGroup (Spec R) ≃+ Additive (CommRing.Pic R)`
sends `[L]` to Mathlib's class of `Γ(Spec R, L)`; tensor products go through the actual
`tildeTensorIso`, and `picardGroupEquivCommRingPic_pullbackClass` matches pullback along
`Spec.map φ` with `CommRing.Pic.mapRingHom φ.hom` through `tildePullbackIso`. On every scheme, `chartReconstructionIso` identifies a line bundle with
the bundle glued from the unit cocycle of chosen charts indexed by the points, so
`small_picardGroup : Small.{u} (PicardGroup X)` holds for `X : Scheme.{u}`; its local
criterion is `Scheme.Modules.isIso_of_forall_bijective_app`. No Noetherian, domain or
finiteness hypothesis is used. The consumers are the Picard functor family
[Picard](../../Picard/README.md), whose fppf comparison uses the local unit charts of
`isLocallyRankOne_iff_restrict_unit` to make every Picard class vanish on a Zariski
covering, and the focused tests `AglibTest.AlgebraicGeometry.Picard.Affine` and
`.ChartCocycle`.

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

[Gluing/Frames](Gluing/Frames.md) constructs `LocalFrames.cocycle` from
actual local unit frames of an arbitrary module sheaf. Its transition unit is
the coefficient in frame `i` of the original generator of frame `j`; inverse,
restriction and cocycle equations are supplied by the construction. When the
frame opens cover the scheme, `LocalFrames.sheafIso` reconstructs the original
module from that cocycle, and `sheafIso_hom_over` retains every original local
frame morphism. `overFrameOfChart` transports a frame on an open immersion to
its actual open range. These interfaces require no quasicoherence, finite cover,
flatness, field or Noetherian hypothesis.

[Gluing/Pullback](Gluing/Pullback.lean) pulls a glued line module back along a scheme
morphism `f : X ⟶ Y`. Take cocycles `c` on a cover `U` of `Y` and `c'` on `U'` with
`f⁻¹(U i) = U' i` and transition units `f^#(c_ij) = c'_ij` (`TransitionPullback`, stable
under `zpow`). Then `pullbackIso` gives `f^* c.sheaf ≅ c'.sheaf` and sends the pulled-back
chart generators to the chart generators. The forward map is adjoint to `toPushforward`,
and the inverse is `toPullback`. Both composites are checked on generators
(`hom_ext_generator`), so no local trivialization of the pullback is computed.

[Gluing/Cohomologous](Gluing/Cohomologous.lean) compares unit cocycles `c`, `c'` on the same cover.
`Cohomologous c c' u` says `c'ᵢⱼ uⱼ = cᵢⱼ uᵢ` for units `uᵢ` on the charts; `sheafIsoOfCohomologous`
glues such units to an isomorphism of the glued sheaves (sending the generator of chart `i` to `uᵢ`
times the generator), and `exists_cohomologous_of_iso` recovers the units from any isomorphism. The
trivial cocycle `1` glues to the structure sheaf (`oneSheafIso`), and `twist` changes the frames by
units. Hence `classOf_lineBundle_eq_iff` and `classOf_lineBundle_eq_zero_iff`: glued line bundles
have equal classes exactly when their cocycles are cohomologous (the torsor form is Stacks, Tag
0B8R). The leaf also has `Scheme.Modules.val_app_smul`, the `f.val.app (op V)` form of Mathlib's
`Scheme.Modules.Hom.app_smul` with the scalar typed in `Γ(X, V)`.
[Gluing/Tensor](Gluing/Tensor.lean) proves that the sheafified tensor product of the glued sheaves
of `c` and `c'` is the glued sheaf of the product cocycle `c * c'` (`tensorIso`, forward map the
section product, as for `ProjectiveSpace.twistingTensorIso`), so `classOf_lineBundle_mul` adds the
classes. [Gluing/PullbackCocycle](Gluing/PullbackCocycle.lean) constructs, for a family `U'` with
`f⁻¹(U i) = U' i`, the cocycle of the pulled-back transition units `f^#(cᵢⱼ)`
(`UnitCocycle.pullbackCocycle`; `ProjectiveSpace.FromSections.pullbackCocycle` is the case
`U' i = f⁻¹(U i)`). The pullback of the glued line bundle has the class of the line bundle glued
from it (`classOf_pullbackLineBundle`). No hypothesis on `X` or on the cover is used beyond
`iSup U = ⊤` and, for the pullback, `f⁻¹(U i) = U' i`. Consumer: `Picard/Tangent/Cech`.

[TensorFunctorAssociator/Sections](TensorFunctorAssociator/Sections.lean)
records the original left/right tensor-unit and nested pure-section
formulas. `moduleLineTensorAssociator_hom_section` and `_inv_section`
use the actual associator, its original sheafification units and the
original two-line trivialization data; the third module is arbitrary.
No new tensor, associator or compatibility assumption is introduced.
The cover and scheme universes remain independent. The source passed
`1792125344557185000-79728` at default budgets; the raw native-map
consumer passed `1792125406028387000-80022`, using the three standard axioms.

[Locus](Locus.lean) defines `IsLocallyRankOneAt M x`: the pullback of `M` along some open immersion through `x` is locally rank one. Its locus is open, `M` is locally rank one iff the condition holds at every point, and a pullback is locally rank one when the image of the morphism lies in the locus. [Tilde](Tilde.lean) proves the converse `invertible_of_tilde_isLocallyRankOne` of `tilde_isLocallyRankOne` and the equivalence `tilde_isLocallyRankOne_iff`. Neither uses a finiteness or Noetherian hypothesis. The consumer is [relative effective Cartier divisors](../../EffectiveCartierDivisor/Relative/README.md).

[DualTensorEquivalence](DualTensorEquivalence.lean) defines
`Scheme.Modules.Invertible.lineBundleDualTensorEquivalence`: tensoring by the
actual dual line bundle is an equivalence of the original module-sheaf category
on every scheme, with tensoring by the original bundle as inverse. Its
cancellation maps use the actual evaluation, associator, braiding and units.
[Power](Power/README.md) documents coherent powers and their pullbacks;
[FinitePresentation](FinitePresentation.lean), [Bidual](Bidual.lean) and
[TensorFaithful](TensorFaithful.lean) retain the original line-bundle objects.

[Root pairs](Root/README.md) retains the actual target power isomorphism and
original pullback maps. Affine square-zero object lifting holds for every `n`;
lifting a prescribed root-pair isomorphism additionally requires
`IsUnit (n : Γ(X, ⊤))`. These results do not assert global, formal, or
henselian root existence.

[RankOne](RankOne.lean) proves `isLocallyRankOne_iff_sheafHasRank_one : IsLocallyRankOne X M ↔ SheafHasRank M 1`. Consumers: [Formal/Algebraization](Formal/Algebraization.lean) and [Grassmannian/LocallyFree](../../Grassmannian/README.md).

## Formal lifting and descent

[Formal](Formal/README.md) documents the square-zero, completion, formal-system
and henselian line-bundle lifting interfaces. In particular,
[Henselian/General](Formal/Henselian/General.lean) proves residue-fibre line-bundle
lifting and surjectivity of the original Picard pullback for any henselian local
ring and proper morphism equipped with an actual affine binary cover. The
complete-base result has the additional Noetherian and adic-completeness
hypotheses recorded there. [Descent](Descent/README.md) describes the actual
binary overlap and limit comparison sources. The projective-line case is a
corollary of the general henselian theorem.

[GeneratingKernel](GeneratingKernel.md) constructs original cross-relation
sections of the kernel of a finite generating row for a line bundle, with
the actual tensor-inclusion formula. The scheme is arbitrary. It supplies
the section-algebra argument on the ordinary rational blowup.
[Bidual/Affine](Bidual/Affine.md) compares actual affine bidual sections and
evaluation with module double duals; over regular local rings of dimension
at most two, finite modules with generic dimension one yield the stated
local line comparison. [Bidual/Map](Bidual/Map.md) proves naturality of
original evaluation and extends a supplied map into an actual line to the
bidual. The one-pole differential consumer supplies that map and its
rank-one target; canonical-module or trace compatibility is not assumed.
