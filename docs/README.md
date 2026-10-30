# Documentation and reading routes

The [source-family guides](../Aglib/README.md) describe the implemented objects,
main results, focused imports and exact hypotheses. This directory coordinates
package-wide conventions, reading routes and the scope of recorded evidence.

| Guide | Purpose |
| --- | --- |
| [Architecture](ARCHITECTURE.md) | Mathematical ownership, dependency direction and extension admission |
| [Naming](NAMING.md) | Native owners, family names, precise leaf imports and naming exceptions |
| [Interfaces](INTERFACES.md) | Canonical maps, universe boundaries, proved suppliers and remaining inputs |
| [Scope](SCOPE.md) | General mathematics admitted here and deferred application layers |
| [Development](DEVELOPMENT.md) | Setup, incremental validation, publication and contribution conventions |
| [Performance](PERFORMANCE.md) | Performance methods, decision process and complete cases under `performance/` |
| [Caching](CACHING.md) | Native Lake artifacts, CI transport, cross-library reuse and provenance |
| [Downstream integration](DOWNSTREAM.md) | Dependency order, inspected pins and application verification boundaries |
| [Etale cohomology migration](ETALE_COHOMOLOGY_MIGRATION.md) | Exact new module/namespace names and the separate Quillen, Motivic and R5Lab handoff |
| [References](REFERENCES.md) | Exact source identities and inspected organization references |
| [Work plan](WORK_PLAN.md) | Current source boundaries and identified historical acceptance checkpoints |
| [Cohomology development](COHOMOLOGY_PLAN.md) | Implemented cohomology endpoints, remaining targets and proof dependencies |
| [Picard scheme development](PICARD_PLAN.md) | Picard functors, descent and representability targets, selected generality and dependencies |
| [Jacobians and curve duality](JACOBIAN_PLAN.md) | General constructions, native Jacobian and curve-cohomology instances, torsion, polarization and Weil pairing proof routes |
| [Zariski–Nagata purity](ZARISKI_NAGATA_PURITY.md) | Finite normal algebras and finite dominant integral morphisms; actual generic separability, source codimension-one conditions and proof dependencies |

## Mathematical routes

| Task | Reading route and conditions |
| --- | --- |
| General Milnor K-theory | [Symbol-family guide](../Aglib/KTheory/MilnorK/README.md). Keep the all-degree group distinct from low-degree tensor presentations, residue hypotheses and characteristic-zero norm interfaces; motivic comparisons stay downstream. |
| Descent | [Scheme descent](../Aglib/AlgebraicGeometry/Descent/README.md), [module descent](../Aglib/AlgebraicGeometry/Descent/Modules/README.md) and [fppf module descent](../Aglib/AlgebraicGeometry/Descent/Modules/Fppf/README.md). The local guides state the cover, flatness, size and coefficient conditions for each construction. |
| Affine modules and coherent sheaves | [ModuleCat](../Aglib/Algebra/Category/ModuleCat/README.md), [affine quasicoherent sheaves](../Aglib/AlgebraicGeometry/Modules/QuasiCoherent/Affine/README.md), then [coherent sheaves](../Aglib/AlgebraicGeometry/Modules/Coherent/README.md). Finite type and finite presentation are distinct; the coherent abelian/exact specialization keeps local Noetherianity. |
| Vector bundles, Picard groups and differentials | [Locally free sheaves](../Aglib/AlgebraicGeometry/Modules/LocallyFree/README.md), [invertible sheaves](../Aglib/AlgebraicGeometry/Modules/Invertible/README.md) and [differentials](../Aglib/AlgebraicGeometry/Modules/Differentials/README.md). These include actual fibre rank, tensor Picard objects, universal derivations, smooth differential rank and etale pullback. |
| Cohomology foundations | [Injective resolutions and Ext](../Aglib/CategoryTheory/Abelian/Injective/README.md), [total complexes](../Aglib/Algebra/Homology/TotalComplex/README.md), [site Cech maps](../Aglib/CategoryTheory/Sites/SheafCohomology/Cech/README.md), [topological sheaves](../Aglib/Topology/Sheaves/README.md), then [scheme cohomology](../Aglib/AlgebraicGeometry/Cohomology/README.md). The comparisons identify the original `Sheaf.H`, scalar action and maps. |
| Base change, proper finiteness and duality | [Base change](../Aglib/AlgebraicGeometry/Cohomology/BaseChange/README.md), [proper finiteness](../Aglib/AlgebraicGeometry/Cohomology/Proper/Finiteness/README.md), [projective-space duality](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/README.md) and [relative projective duality](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Relative/README.md). Retain each endpoint's flatness, Noetherian/coherent or separated-base/chosen-embedding conditions; general proper duality remains separate. |
| Tensor and projection formulas | [Linear algebra](../Aglib/LinearAlgebra/README.md), [canonical site tensor](../Aglib/Algebra/Category/ModuleCat/Sheaf/Tensor/README.md), [scheme tensor](../Aglib/AlgebraicGeometry/Modules/Tensor/README.md), then [projection formula](../Aglib/AlgebraicGeometry/Modules/ProjectionFormula/README.md). The local guides distinguish arbitrary coefficients from finite-locally-free isomorphism results. |
| Complexes and derived calculations | [Ordinary complexes](../Aglib/AlgebraicGeometry/Modules/Complex/README.md), [Godement](../Aglib/AlgebraicGeometry/Cohomology/Godement/README.md) and [good truncation](../Aglib/Algebra/Homology/Embedding/CochainComplex/README.md). Ordinary categorical exactness, bounded augmentation and original-unit derived computations have different premises. |
| Perfect complexes | [Perfect-complex guide](../Aglib/AlgebraicGeometry/Modules/PerfectComplexes/README.md). Chain categories, native derived local models and strict exactness are distinct; local homology bounds do not require the compactness needed for one global interval. |
| Smooth and normal geometry | [Regular-local algebra](../Aglib/RingTheory/RegularLocalRing/README.md), [stalks](../Aglib/AlgebraicGeometry/Stalk/README.md), [etale morphisms](../Aglib/AlgebraicGeometry/Morphisms/Etale/README.md), [smooth morphisms](../Aglib/AlgebraicGeometry/Morphisms/Smooth/README.md), [normal properties](../Aglib/AlgebraicGeometry/Properties/Normal/README.md) and [geometric connectedness](../Aglib/AlgebraicGeometry/Geometrically/Connected/README.md). Each retains its own scheme, morphism and base-field conditions. |
| Finite-etale objects and rigidity | [Finite-etale objects](../Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/README.md), [finite-morphism lifts](../Aglib/AlgebraicGeometry/Morphisms/Finite/README.md), [unramified algebra](../Aglib/RingTheory/Unramified/README.md) and [section rigidity](../Aglib/AlgebraicGeometry/Morphisms/FormallyUnramified/README.md). Empty covers and empty finite lift sets are allowed; geometric-point existence and rigidity retain separate hypotheses. |
| Ideals, Cartier criteria and localization | [Ideal sheaves](../Aglib/AlgebraicGeometry/IdealSheaf/README.md), [effective Cartier ideals](../Aglib/AlgebraicGeometry/EffectiveCartierDivisor/README.md), [coherent extension](../Aglib/AlgebraicGeometry/Modules/Coherent/Extension/README.md) and [Serre localization](../Aglib/AlgebraicGeometry/Modules/Coherent/Localization/README.md). Arbitrary-base Cartier criteria and local/global Noetherian coherent hypotheses remain distinct. |

## Source correspondence and evidence

[TT foundations](migration/tt-foundations.json) and
[R5 general finite-etale theory](migration/r5-general-etale.json) identify their
recorded source cuts. Earlier selections are retained in
[latest-quillen](migration/latest-quillen.json),
[latest-scheme](migration/latest-scheme.json),
[latest-homology](migration/latest-homology.json) and
[latest-general-cuts](migration/latest-general-cuts.json).
[Module](module-map.json) and [namespace](namespace-map.json) maps record
successive refinements and retirements, including intermediate names.

The [R5 source/native correspondence](migration/R5_SOURCE_CORRESPONDENCE.md)
links the frozen full-source baseline to exact native map and guard arguments,
including retained mathematical premises and current producer frontiers.

These records describe their identified source and validation snapshots. A
historical `latest` filename or `current_identity_validation` field is not a
live inventory or acceptance claim for every later checkout. Keep original
hashes and evidence fixed; use the family guides for present interfaces and
[WORK_PLAN.md](WORK_PLAN.md) for the scope of acceptance checkpoints. Source
correspondence and successful checks do not supply an unproved theorem family.
