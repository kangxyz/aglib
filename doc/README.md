# Documentation and reading routes

The [source-family guides](../Aglib/README.md) record both reusable interfaces and main mathematical results, with focused imports, actual hypotheses and present consumers. This directory owns the package-wide reading routes and evidence boundary.

| Guide | Purpose |
| --- | --- |
| [Architecture](ARCHITECTURE.md) | Overall design principles, mathematical ownership, dependency direction and extension admission |
| [Naming](NAMING.md) | Concrete conventions, native owners, compound exceptions and examples for future extensions |
| [Interfaces](INTERFACES.md) | Native owners, canonical maps, universe boundaries and explicit theorem-family inputs |
| [Scope](SCOPE.md) | General mathematics admitted here and deferred application layers |
| [Development](DEVELOPMENT.md) | Setup, focused builds, integration checks, publication and [contribution conventions](DEVELOPMENT.md#contribution-conventions) |
| [Performance](PERFORMANCE.md) | Measured kernel costs, source-based diagnostics and interface-preserving optimizations |
| [Caching](CACHING.md) | Native Lake artifacts, cross-library reuse, shared CI transport and provenance |
| [Downstream integration](DOWNSTREAM.md) | Quillen and R5Lab dependency order, compatibility boundaries and application verification |
| [References](REFERENCES.md) | Exact source identities and inspected organization references |
| [Work plan](WORK_PLAN.md) | Current source/integration coverage and remaining work |

For affine module theory, start with [ModuleCat](../Aglib/Algebra/Category/ModuleCat/README.md), then [quasicoherent affine sheaves](../Aglib/AlgebraicGeometry/Modules/QuasiCoherent/Affine/README.md). Finite type and finite presentation are distinct object properties. [Coherent sheaves](../Aglib/AlgebraicGeometry/Modules/Coherent/README.md) supplies the locally Noetherian abelian/exact specialization. Finite and closed-immersion direct image uses the actual geometric functors and affine scalar comparisons.

For vector bundles, start with [locally free sheaves](../Aglib/AlgebraicGeometry/Modules/LocallyFree/README.md), its finite-local-basis class and local splitting. The pointwise fibre-dimension theorem supplies the rank interface. [Invertible sheaves](../Aglib/AlgebraicGeometry/Modules/Invertible/README.md) separately constructs the ordinary tensor Picard group and additive arbitrary pullback. [Differential sheaves](../Aglib/AlgebraicGeometry/Modules/Differentials/README.md) gives actual universal derivations and etale pullback, with proved smooth rank and canonical etale differential pullback.

For cohomology, read [generic resolution and exact-functor comparison](../Aglib/CategoryTheory/Abelian/Injective/README.md), [total complexes](../Aglib/Algebra/Homology/TotalComplex/README.md), [generic site Cech maps](../Aglib/CategoryTheory/Sites/SheafCohomology/Cech/README.md) and [topological sheaf sections](../Aglib/Topology/Sheaves/README.md). The [scheme cohomology](../Aglib/AlgebraicGeometry/Cohomology/README.md) route then constructs structural scalars, proves affine/finite-support comparisons, and identifies canonical Cech and field-base-change maps with the original `Sheaf.H`.

For geometry, read [regular-local algebra](../Aglib/RingTheory/RegularLocalRing/README.md), [scheme stalks](../Aglib/AlgebraicGeometry/Stalk/README.md), [etale morphisms](../Aglib/AlgebraicGeometry/Morphisms/Etale/README.md), then [smooth morphisms](../Aglib/AlgebraicGeometry/Morphisms/Smooth/README.md). [Normal scheme properties](../Aglib/AlgebraicGeometry/Properties/Normal/README.md) and [geometric connectedness](../Aglib/AlgebraicGeometry/Geometrically/Connected/README.md) preserve their distinct object/base-field conditions.

The [canonical site tensor](../Aglib/Algebra/Category/ModuleCat/Sheaf/Tensor/README.md) feeds [scheme tensors](../Aglib/AlgebraicGeometry/Modules/Tensor/README.md), finite-free/projective affine reductions and actual [projection formula](../Aglib/AlgebraicGeometry/Modules/ProjectionFormula/README.md). The [ordinary module-complex route](../Aglib/AlgebraicGeometry/Modules/Complex/README.md) gives geometric restriction, flat pullback and acyclicity on specified opens. The [Godement route](../Aglib/AlgebraicGeometry/Cohomology/Godement/README.md) distinguishes ordinary-complex categorical exactness from bounded augmentation, original-unit D+ calculation and conditional local-unit descent. [Good truncation](../Aglib/Algebra/Homology/Embedding/CochainComplex/README.md), stupid layers and two-bound triangulated comparison provide the selected generic derived interfaces.

For structural perfect complexes, continue from ordinary complexes to the [perfect-complex guide](../Aglib/AlgebraicGeometry/Modules/PerfectComplexes/README.md). It distinguishes the full chain categories, actual native derived local models and strict exactness; its homology results separate arbitrary-scheme local bounds from the global homology interval under `CompactSpace X`.

For finite-etale objects and their canonical field-valued fibres/base change, read [FiniteEtale](../Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/README.md). The [finite-morphism point-lift guide](../Aglib/AlgebraicGeometry/Morphisms/Finite/README.md) supplies the weaker finite-Hom result over arbitrary fields, with empty lift sets allowed. The [unramified algebra](../Aglib/RingTheory/Unramified/README.md) and [formally unramified section](../Aglib/AlgebraicGeometry/Morphisms/FormallyUnramified/README.md) rigidity guides state their separate map-equality interfaces and exact premises.

Current source correspondence is recorded in [TT foundations](migration/tt-foundations.json) and [R5 general finite-etale theory](migration/r5-general-etale.json). The earlier source selections remain in [latest-quillen](migration/latest-quillen.json), [latest-scheme](migration/latest-scheme.json), [latest-homology](migration/latest-homology.json) and [latest-general-cuts](migration/latest-general-cuts.json). These provenance records identify source cuts and native destinations; the family guides retain the bounds and input families, and [WORK_PLAN.md](WORK_PLAN.md) distinguishes historical coverage from current integration.


[Linear algebra](../Aglib/LinearAlgebra/README.md) owns the tensor-product map and
injectivity comparison route. For actual ideal modules and arbitrary-base
relative Cartier consequences, read [ideal sheaves](../Aglib/AlgebraicGeometry/IdealSheaf/README.md)
then [effective Cartier ideals](../Aglib/AlgebraicGeometry/EffectiveCartierDivisor/README.md).
[Coherent extension](../Aglib/AlgebraicGeometry/Modules/Coherent/Extension/README.md)
and [Serre localization](../Aglib/AlgebraicGeometry/Modules/Coherent/Localization/README.md)
retain their distinct local and global Noetherian hypotheses.

The source authority and exact new selections are [latest-quillen](migration/latest-quillen.json), [latest-scheme](migration/latest-scheme.json), [latest-homology](migration/latest-homology.json) and [latest-general-cuts](migration/latest-general-cuts.json). These provenance records do not replace the source's bounds or input families.

[Cohomology development](COHOMOLOGY_PLAN.md) records the current affine/flat base-change, projective finiteness, duality and proper-base-change targets and their exact proof boundaries.
