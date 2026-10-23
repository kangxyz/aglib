# Abelian object properties and resolutions

[Subcategory](Subcategory/README.md) constructs an abelian full subcategory from containing-zero, subobject, quotient and finite-product closure. [SerreClass](SerreClass/README.md) separately derives finite-product closure from a genuine Serre class. The former result does not acquire an extension-closure premise from the latter.

[Injective](Injective/README.md) gives actual kernel short exact sequences of supplied resolutions and comparison of exact-functor Ext maps with actual mapped resolution cycles. These generic statements feed finite-module/coherent structures and scheme Cech/cohomology comparison. Focused imports follow their subfamily source paths.

[Ext1](Ext1/README.md) realizes every degree-one Ext class by a short exact extension with fixed endpoints, and turns equality of classes into an endpoint-preserving isomorphism of extensions. The category is arbitrary abelian, with the stated independent `HasExt` and derived-category universes; no enough-injective or enough-projective premise is added.

[FiniteCoproductFunctor](FiniteCoproductFunctor.lean) supplies finite-limit and finite-colimit preservation for the actual finite coproduct functor in the stated abelian setting. This lower categorical result is used by finite-free sheaf tensor exactness.

[Regular](Regular.lean) proves
`Abelian.exists_generalizedInverse_of_projective_cokernel`. A morphism
with projective target and projective original cokernel admits an actual
generalized inverse. The construction splits the original image sequence,
then the original epimorphism onto that image. Projectivity of the source
or kernel is not required. The pointwise homology/base-change criteria use
this native splitting.

[ExtensionPushout](ExtensionPushout.lean) constructs the actual pushout of a
short exact sequence in an arbitrary abelian category and proves its exactness.
Its Ext-class comparison identifies coefficient change with this pushout,
retaining the displayed Ext and universe assumptions. This is a lower input
to the finite-etale torsor and cohomology comparisons.

`projective_kernel_iff_of_generalizedInverse` assumes a projective target
and an actual generalized inverse. Projectivity of the original kernel is
then equivalent to projectivity of the source, by the two actual
retractions. It does not require a projective cokernel as a separate input.

[PresentationEffectivity](PresentationEffectivity.lean) algebraizes an
object with a two-term presentation by image objects of a full functor between
abelian categories that preserves zero morphisms and finite colimits. It lifts
the relation map and takes its native cokernel, retaining the quotient arrow.
The alternative input is an epimorphism onto the object and an epimorphism onto
its categorical kernel; existence of either presentation remains explicit.

[ReductionKernel](ReductionKernel.lean) gives epimorphisms on ordinary relation
kernels for a right exact reduction with epimorphic units. It does not assert
preservation of kernels. [KernelSquare](KernelSquare.lean) interchanges the two
kernels of a commutative square while retaining the double inclusions.
[KernelSquareExact](KernelSquareExact.lean) gives the correction argument for
surjectivity on the other pair of kernels when the upper arrow and the
relation-kernel map are epimorphisms.

[CoproductKernels](CoproductKernels.lean) identifies the coproduct of component
kernels with the kernel of the coproduct map in an AB4 abelian category,
retaining the kernel inclusion and allowing an independent, arbitrary index
universe. [CoproductKernelTransport](CoproductKernelTransport.lean) transports
this comparison through a finite-limit-preserving functor and a specified
commuting coproduct square. Its geometric consumer is the coherent graded
relation kernel in [Grothendieck existence](../../AlgebraicGeometry/Cohomology/GrothendieckExistence/README.md).

[KernelCompEpi](KernelCompEpi.lean): if `i` is a kernel of `q` and `μ` is an epimorphism, then a
map `k` from a kernel of `μ ≫ q` with `k ≫ i = ιK ≫ μ` is an epimorphism
(`Abelian.epi_of_isKernel_comp`), as a pullback of an epimorphism. Consumer: the direct image of the
twisted ideal sheaf of a Hilbert family
([HilbertScheme/IdealTwist/DirectImage](../../AlgebraicGeometry/HilbertScheme/IdealTwist/DirectImage.lean)).
