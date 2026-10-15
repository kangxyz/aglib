# Documentation and reading routes

The [source-family guides](../Aglib/README.md) record both reusable interfaces and main mathematical results, with focused imports, actual hypotheses and present consumers. This directory owns the package-wide reading routes and evidence boundary.

| Guide | Purpose |
| --- | --- |
| [Architecture](ARCHITECTURE.md) | Overall design principles, mathematical ownership, dependency direction and extension admission |
| [Naming](NAMING.md) | Concrete conventions, native owners, compound exceptions and examples for future extensions |
| [Interfaces](INTERFACES.md) | Native owners, canonical maps, universe boundaries and explicit theorem-family inputs |
| [Scope](SCOPE.md) | General mathematics admitted here and deferred application layers |
| [Development](DEVELOPMENT.md) | Setup, focused builds, integration checks, publication and [contribution conventions](DEVELOPMENT.md#contribution-conventions) |
| [Downstream integration](DOWNSTREAM.md) | Quillen and R5Lab dependency order, compatibility boundaries and application verification |
| [References](REFERENCES.md) | Exact source identities and inspected organization references |
| [Work plan](WORK_PLAN.md) | Current source/integration coverage and remaining work |

For affine module theory, start with [ModuleCat](../Aglib/Algebra/Category/ModuleCat/README.md), then [quasicoherent affine sheaves](../Aglib/AlgebraicGeometry/Modules/QuasiCoherent/Affine/README.md). Finite type and finite presentation are distinct object properties. [Coherent sheaves](../Aglib/AlgebraicGeometry/Modules/Coherent/README.md) supplies the locally Noetherian abelian/exact specialization. Finite and closed-immersion direct image uses the actual geometric functors and affine scalar comparisons.

For vector bundles, start with [locally free sheaves](../Aglib/AlgebraicGeometry/Modules/LocallyFree/README.md), its finite-local-basis class and local splitting. The rank interface retains its fibre-dimension input. [Invertible sheaves](../Aglib/AlgebraicGeometry/Modules/Invertible/README.md) separately constructs the ordinary tensor Picard group and additive arbitrary pullback. [Differential sheaves](../Aglib/AlgebraicGeometry/Modules/Differentials/README.md) gives actual universal derivations and etale pullback, with smooth rank retained as an input.

For cohomology, read [generic resolution and exact-functor comparison](../Aglib/CategoryTheory/Abelian/Injective/README.md), [total complexes](../Aglib/Algebra/Homology/TotalComplex/README.md), [generic site Cech maps](../Aglib/CategoryTheory/Sites/SheafCohomology/Cech/README.md) and [topological sheaf sections](../Aglib/Topology/Sheaves/README.md). The [scheme cohomology](../Aglib/AlgebraicGeometry/Cohomology/README.md) route then constructs structural scalars, proves affine/finite-support comparisons, and identifies canonical Cech and field-base-change maps with the original `Sheaf.H`.

For geometry, read [regular-local algebra](../Aglib/RingTheory/RegularLocalRing/README.md), [scheme stalks](../Aglib/AlgebraicGeometry/Stalk/README.md), [etale morphisms](../Aglib/AlgebraicGeometry/Morphisms/Etale/README.md), then [smooth morphisms](../Aglib/AlgebraicGeometry/Morphisms/Smooth/README.md). [Normal scheme properties](../Aglib/AlgebraicGeometry/Properties/Normal/README.md) and [geometric connectedness](../Aglib/AlgebraicGeometry/Geometrically/Connected/README.md) preserve their distinct object/base-field conditions.

The [canonical site tensor](../Aglib/Algebra/Category/ModuleCat/Sheaf/Tensor/README.md) feeds [scheme tensors](../Aglib/AlgebraicGeometry/Modules/Tensor/README.md), finite-free/projective affine reductions and actual [projection formula](../Aglib/AlgebraicGeometry/Modules/ProjectionFormula/README.md). The [ordinary module-complex route](../Aglib/AlgebraicGeometry/Modules/Complex/README.md) gives geometric restriction, flat pullback and acyclicity on specified opens. The [Godement route](../Aglib/AlgebraicGeometry/Cohomology/Godement/README.md) distinguishes ordinary-complex categorical exactness from bounded augmentation, original-unit D+ calculation and conditional local-unit descent. [Good truncation](../Aglib/Algebra/Homology/Embedding/CochainComplex/README.md), stupid layers and two-bound triangulated comparison provide the selected generic derived interfaces.

The source authority and exact new selections are [latest-quillen](migration/latest-quillen.json), [latest-scheme](migration/latest-scheme.json), [latest-homology](migration/latest-homology.json) and [latest-general-cuts](migration/latest-general-cuts.json). These provenance records do not replace the source's bounds or input families.
