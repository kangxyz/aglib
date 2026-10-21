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
| [DirectImage](DirectImage/README.md) | Native resolution sections, qcqs quasicoherent higher images and proper coherent higher images over locally Noetherian targets |
| [FiniteModel](FiniteModel/README.md) and [Proper/FiniteModel](Proper/FiniteModel/README.md) | One bounded finite-projective model for proper coherent relatively flat coefficients over a Noetherian affine base, including every ring base change |
| [Proper/Finiteness](Proper/Finiteness/README.md) and [Proper/Field](Proper/Field/README.md) | Proved proper coherent finiteness and the retained field-valued family suppliers |
| [FormalFunctions](FormalFunctions/README.md) | Canonical completion comparison with original cohomology and geometric thickening towers for proper coherent coefficients, including local higher-image stalks |
| [Duality](Duality/README.md) and [projective duality](Duality/Projective/README.md) | Original residue/derived traces, relative projective coherent duality over Noetherian separated bases and the chosen smooth-embedding canonical comparison |

Proved interfaces include positive affine quasicoherent vanishing over every commutative affine ring, skyscraper positive vanishing at any point and Noetherian vanishing above a topological dimension bound. Affine module base change allows arbitrary geometric base change. The original flat base-change map is invertible for qcqs morphisms and quasicoherent coefficients; its [D+ version](BaseChange/Derived/README.md) holds over arbitrary bases for bounded-below objects with quasicoherent original homology. Proper coherent finiteness holds over Noetherian affine bases, and actual coherent higher direct images descend to every locally Noetherian target. The retained field-valued finiteness families have proved suppliers.

[Projective duality](Duality/Projective/README.md) proves complementary-degree coherent Serre duality over fields and all-degree derived duality for coherent sources over Noetherian affine bases with every base module. The [relative family](Duality/Projective/Relative/README.md) constructs the original differential trace over separated bases and proves coherent duality over Noetherian separated bases for arbitrary quasicoherent base coefficients, with a supplied projective-space square. Transfer through a chosen closed embedding retains the actual right-adjoint coefficient; its smooth unit-coefficient specialization uses the [proved canonical comparison](Duality/Projective/Canonical.lean) and one original trace. General proper duality, embedding independence and coefficient-complex/internal-RHom extensions remain separate. The full arbitrary-base `LocalFreeCohomologyBaseChange` family, general nonflat higher-image sheaf comparison and direct images of arbitrary perfect coefficients also remain open interfaces.

Lower [injective/Ext](../../CategoryTheory/Abelian/Injective/README.md), [total-complex](../../Algebra/Homology/TotalComplex/README.md), [generic site Cech](../../CategoryTheory/Sites/SheafCohomology/Cech/README.md) and [topological sheaf](../../Topology/Sheaves/README.md) results precede scheme specialization. [Actual module sheaves](../Modules/README.md) supply geometric functors, stalks, presentations and base-change maps. Field-linear results do not become arbitrary-base-ring theorems merely because relative evaluation allows an arbitrary base.

The canonical [Godement](Godement/README.md), [local-QI detection](Locality/README.md) and [D+ projection formula](ProjectionFormula/README.md) families retain actual derived direct-image, flat-square and original-unit comparisons. Godement totalization is categorically exact on ordinary complexes; its augmentation/QI/derived calculation retains bounded-below membership or an explicit lower bound. These lower constructions and the geometric endpoint suppliers above have distinct hypotheses and roles.

[Formal functions](FormalFunctions/README.md) identifies the canonical map
from the adic completion of original cohomology to its compatible quotient
and geometric thickening towers, for a proper scheme over a Noetherian affine
base, every coherent coefficient, ideal and nonnegative degree. Complete-base
identification retains adic completeness; the higher-direct-image stalk version
allows a locally Noetherian target. No flatness, projective embedding or
additional Rees-finiteness premise is needed. General Grothendieck existence,
Artin approximation and object effectivity remain external.

[Ordinary stalks and fibre sections](Proper/FibreIdempotents.md) constructs the
canonical ordinary pushforward-stalk map to literal-fibre global sections and
its germ and residue factorization for arbitrary morphisms. When `f.c` is an
isomorphism, its image consists of residue constants. The proper
[affine image theorem](Proper/FibreFormalFunctions.lean) gives an arbitrary
global-function preimage for each idempotent on any ideal thickening over a
Noetherian ring. Its [stalk specialization](Proper/FibreFormalFunctions/Stalk.lean)
gives an arbitrary ordinary-stalk preimage for each literal-fibre idempotent
over a locally Noetherian target. The
[connectedness theorem](../Morphisms/Proper/ConnectedFibres.md) proves geometric
connectedness for proper surjective `f` over a locally Noetherian target with
`IsIso f.c`, using the direct affine image route and actual flat base change.
