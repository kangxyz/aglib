# Actual Zariski cohomology

The object is Mathlib's additive `Sheaf.H` on the actual Zariski opens site. Schemes and coefficient fields in universe `u` give Ext-defined cohomology in `Type (u+1)`, in natural-number degrees. Generic additive-sheaf results allow arbitrary schemes; field-linear interfaces retain the actual structural field map.

| Subfamily | Interfaces and main results |
| --- | --- |
| [Modules](Modules/README.md) | Actual coefficients, arbitrary structural-ring actions, H0, original module Ext comparison and coefficient maps |
| [Restriction](Restriction/README.md) | Native open `Sheaf.H'` compared with original cohomology of the actual restricted module, retaining structural scalars |
| [Functoriality](Functoriality/README.md) | Exact-inverse-image coefficient pullback, structural linear/semilinear maps and isomorphism invariance |
| [Injective](Injective/README.md) and [Flasque](Flasque/README.md) | Actual resolution section cycles, restriction, degree-zero normalization and flasque acyclicity |
| [Affine](Affine/README.md) | Quasicoherent affine acyclicity, affine direct-image acyclicity and actual H1 comparison |
| [Cech](Cech/README.md) | Principal-cover exactness and scalar/natural comparison with original `Sheaf.H` |
| [MayerVietoris](MayerVietoris/README.md) | Genuine two-open sequences, two-affine higher vanishing and H1 restriction cokernel |
| [Exact](Exact/README.md) and [Finiteness](Finiteness/README.md) | Actual linear connecting maps, exactness, conditional finiteness transfer and low-degree Euler consequences |
| [Support](Support/README.md) and [Vanishing](Vanishing/README.md) | Skyscraper/finite-closed-support calculations and Noetherian topological-dimension vanishing |
| [BaseChange](BaseChange/README.md) | Original tensor mates and all-degree qcqs flat base change for arbitrary quasicoherent module coefficients |
| [Projective](Projective/README.md) | Finite free twist cohomology over arbitrary rings and all-degree coherent finiteness through an actual embedding in Noetherian polynomial projective space |
| [DirectImage](DirectImage/README.md) | Native injective-resolution global sections, their actual cohomology and coefficient naturality |
| [Duality](Duality/README.md) | Native Laurent residue pairing and finite free duality prerequisites |

Principal unconditional theorem interfaces include positive affine quasicoherent vanishing over every commutative affine ring, skyscraper positive vanishing at any point, Noetherian vanishing above a topological dimension bound, and invertibility of the original cohomology tensor map for qcqs morphisms over spectra along any flat ring map, with arbitrary quasicoherent coefficients in every degree. Affine module base change is proved for arbitrary geometric base change. Coherent coefficients on polynomial projective space over a Noetherian ring, and on schemes with an actual closed embedding into it, have finite original cohomology in every degree. Proper coherent finiteness, Serre duality, higher-direct-image/derived flat base change and the complete relative cohomology/base-change suite remain under development; their retained families are not supplied by the finite-complex prerequisites alone.

Lower [injective/Ext](../../CategoryTheory/Abelian/Injective/README.md), [total-complex](../../Algebra/Homology/TotalComplex/README.md), [generic site Cech](../../CategoryTheory/Sites/SheafCohomology/Cech/README.md) and [topological sheaf](../../Topology/Sheaves/README.md) results precede scheme specialization. [Actual module sheaves](../Modules/README.md) supply geometric functors, stalks, presentations and base-change maps. Field-linear results do not become arbitrary-base-ring theorems merely because relative evaluation allows an arbitrary base.

The latest local Quillen surface adds canonical [Godement](Godement/README.md), [local-QI detection](Locality/README.md) and [D+ projection formula](ProjectionFormula/README.md), plus actual derived direct-image, flat-square and original-unit comparisons. Godement totalization is categorically exact on ordinary complexes; its augmentation/QI/derived calculation retains bounded-below membership or an explicit lower bound. These constructions do not discharge the explicit proper-finiteness, differential-rank, fibre-dimension or relative-cohomology-base-change input families already recorded here.
