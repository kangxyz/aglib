# Actual Zariski cohomology

The object is Mathlib's additive `Sheaf.H` on the actual Zariski opens site. Schemes and coefficient fields in universe `u` give Ext-defined cohomology in `Type (u+1)`, in natural-number degrees. Generic additive-sheaf results allow arbitrary schemes; field-linear interfaces retain the actual structural field map.

| Subfamily | Interfaces and main results |
| --- | --- |
| [Modules](Modules/README.md) | Actual structure/module coefficients, constants, scalar actions, H0 and coefficient maps |
| [Functoriality](Functoriality/README.md) | Exact-inverse-image coefficient pullback, structural linear/semilinear maps and isomorphism invariance |
| [Injective](Injective/README.md) and [Flasque](Flasque/README.md) | Actual resolution section cycles, restriction, degree-zero normalization and flasque acyclicity |
| [Affine](Affine/README.md) | Quasicoherent affine acyclicity, affine direct-image acyclicity and actual H1 comparison |
| [Cech](Cech/README.md) | Principal-cover exactness and scalar/natural comparison with original `Sheaf.H` |
| [MayerVietoris](MayerVietoris/README.md) | Genuine two-open sequences, two-affine higher vanishing and H1 restriction cokernel |
| [Exact](Exact/README.md) and [Finiteness](Finiteness/README.md) | Actual linear connecting maps, exactness, conditional finiteness transfer and low-degree Euler consequences |
| [Support](Support/README.md) and [Vanishing](Vanishing/README.md) | Skyscraper/finite-closed-support calculations and Noetherian topological-dimension vanishing |
| [BaseChange](BaseChange/README.md) | Constructed tensor mate/comparisons, all-degree quasi-compact separated field base change and explicit relative input |

Principal unconditional theorem interfaces include positive affine quasicoherent vanishing over every commutative affine ring, skyscraper positive vanishing at any point, Noetherian vanishing above a topological dimension bound, and bijectivity of the original field-tensor map for quasi-compact separated field schemes in every degree. Proper module finiteness and relative locally free cohomology base change remain explicit inputs on the actual objects/maps.

Lower [injective/Ext](../../CategoryTheory/Abelian/Injective/README.md), [total-complex](../../Algebra/Homology/TotalComplex/README.md), [generic site Cech](../../CategoryTheory/Sites/SheafCohomology/Cech/README.md) and [topological sheaf](../../Topology/Sheaves/README.md) results precede scheme specialization. [Actual module sheaves](../Modules/README.md) supply geometric functors, stalks, presentations and base-change maps. Field-linear results do not become arbitrary-base-ring theorems merely because relative evaluation allows an arbitrary base.

The latest local Quillen surface adds canonical [Godement](Godement/README.md), [local-QI detection](Locality/README.md) and [D+ projection formula](ProjectionFormula/README.md), plus actual derived direct-image, flat-square and original-unit comparisons. Godement totalization is categorically exact on ordinary complexes; its augmentation/QI/derived calculation retains bounded-below membership or an explicit lower bound. These constructions do not discharge the explicit proper-finiteness, differential-rank, fibre-dimension or relative-cohomology-base-change input families already recorded here.
