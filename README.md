# Aglib

`Aglib` is a Lean library of commutative algebra, scheme-module theory and general Zariski cohomology. Its import root is `Aglib`. Declarations extend native mathematical owners such as `Module`, `Algebra`, `CategoryTheory` and `AlgebraicGeometry.Scheme`; original R5Lab and Quillen names are provenance.

The library uses Mathlib's actual rings, categories, schemes, module sheaves and `Sheaf.H`. It supplies reusable objects and canonical maps together with theorem interfaces describing their properties.

| Entry guide | Principal reusable interfaces |
| --- | --- |
| [RingTheory](Aglib/RingTheory/README.md) | Descent data and equalizer algebras, regular-local parameters, support, filtrations, length and scalar Euler expressions |
| [Algebra](Aglib/Algebra/README.md) | Finite-module functors, localized exactness, mapping cones and first-quadrant total complexes |
| [CategoryTheory](Aglib/CategoryTheory/README.md) | Selected exact structures, exact functors, abelian subcategories, small models, injective resolutions and site Cech comparisons |
| [Topology/Sheaves](Aglib/Topology/Sheaves/README.md) | Section complexes, basis detection, Mayer–Vietoris and Noetherian-space sheaf support |
| [AlgebraicGeometry](Aglib/AlgebraicGeometry/README.md) | Actual scheme modules, quasicoherence, presentations, locally free/coherent/invertible/differential sheaves, morphism properties and cohomology |

## Main mathematical results

The owning guides give focused imports, canonical declaration names and the precise source statements.

| Result | Conditions and conclusion |
| --- | --- |
| [Regular-local domain and normality](Aglib/RingTheory/RegularLocalRing/README.md) | A commutative regular local ring is a domain and integrally closed. Positive-dimensional regular local rings admit a scalar-regular first parameter with regular quotient and dimension drop one. |
| [Tensor products of domains](Aglib/RingTheory/TensorProduct/README.md) | Over an algebraically closed field, the tensor product of two arbitrary commutative domain algebras is a domain; no finite-type assumption is made on the final algebras. |
| [Finite length from support](Aglib/RingTheory/FiniteLength/README.md) | A finite module over a Noetherian commutative ring has finite length when every prime of its actual support is maximal. Canonical localization-length comparisons retain their separate flatness or surjectivity hypotheses. |
| [Affine quasicoherent comparison and acyclicity](Aglib/AlgebraicGeometry/Modules/QuasiCoherent/Affine/README.md) | Actual quasicoherent sheaves on an affine scheme have the native module/tilde comparison. Their positive Zariski cohomology vanishes over every commutative affine ring, without Noetherianity. |
| [Exact vector-bundle pullback](Aglib/AlgebraicGeometry/Modules/LocallyFree/README.md) | Finite locally free sheaves form an exact category. Pullback along an arbitrary scheme morphism preserves its short exact sequences, by local splitting; no flatness of the morphism is required. |
| [Smooth field-scheme geometry](Aglib/AlgebraicGeometry/Morphisms/Smooth/README.md) | Smooth schemes over arbitrary fields have regular and normal stalks. Relative dimension `n` bounds every stalk dimension by `n`; equality holds at closed points, and the scheme dimension is `n` when the scheme is nonempty. |
| [Normal components](Aglib/AlgebraicGeometry/Properties/Normal/README.md) | Domain stalks on a locally Noetherian scheme give open irreducible components. A connected locally Noetherian scheme with domain and integrally closed stalks is integral. |
| [Ordinary Picard-group pullback](Aglib/AlgebraicGeometry/Modules/Invertible/README.md) | Actual rank-one module sheaves on every scheme give an ordinary additive Picard group by tensor and duality. Every scheme morphism induces an additive pullback map. |
| [Canonical cohomology field base change](Aglib/AlgebraicGeometry/Cohomology/BaseChange/README.md) | For a quasi-compact separated scheme over a field, extension of that field makes the constructed structure-cohomology tensor map bijective in every nonnegative degree; no finite-generation premise is used. |
| [Noetherian cohomological dimension](Aglib/AlgebraicGeometry/Cohomology/Vanishing/README.md) | For every abelian sheaf on a Noetherian scheme of topological Krull dimension at most `d`, its actual Zariski `Sheaf.H` vanishes in degrees greater than `d`. Properness and quasicoherence are not required. |

The library also exposes conditional result interfaces from explicit general inputs. Proper module-cohomology finiteness requires `ProperModuleCohomologyFinite`; smooth differential rank requires `SmoothDifferentialRank`; local-basis fibre/rank comparisons require `LocalBasisFibreDimension`; and relative locally free cohomology base change requires `LocalFreeCohomologyBaseChange`. The [interface guide](doc/INTERFACES.md) states these families on their actual objects and maps. The new Godement resolutions and derived interfaces do not discharge these R5 inputs. Build and foundation checks do not supply them.


The latest local Quillen surface adds these general result interfaces:

| Result | Conditions and conclusion |
| --- | --- |
| [Affine vector-bundle sections](Aglib/AlgebraicGeometry/Modules/LocallyFree/Affine/README.md) | A finite locally free sheaf on `Spec R` has finitely presented projective global sections over any commutative ring, with an actual finite-free retract. |
| [Projection formula](Aglib/AlgebraicGeometry/Modules/ProjectionFormula/README.md) | For arbitrary scheme morphisms the target coefficient is finite locally free; for closed immersions both module coefficients may be arbitrary. The isomorphism uses the actual projection map. |
| [Godement totalization](Aglib/AlgebraicGeometry/Cohomology/Godement/TotalComplex/README.md) | Totalization preserves categorical short exactness on ordinary integer complexes, including unbounded objects. Augmentation/QI and D+ calculation retain bounded-below membership or an explicit strict lower term bound. |
| [D+ triangles and bounded comparison](Aglib/Algebra/Homology/DerivedCategory/Plus/README.md) | Actual short exact bounded-below complexes give distinguished triangles in an abelian derived setting. Single-term comparison retains both actual lower and upper term bounds; a derived contraction gives only the stated one-sided unit-compatible isomorphism. |
| [Derived open-cover detection](Aglib/AlgebraicGeometry/Cohomology/Locality/README.md) | A jointly covering family of actual open immersions detects isomorphisms and zero objects in the bounded-below derived module category, from the corresponding actual local hypotheses. |
| [Affine induction](Aglib/AlgebraicGeometry/Properties/README.md) | On qcqs schemes, an isomorphism-invariant property follows from its affine case and compact binary-union closure with the overlap property supplied. |


## Use and source basis

The aggregate import is `import Aglib`. The family guides identify focused imports for individual results; production implementations use precise lower leaves. [Positive interface fixtures](AglibTest) and [the independent consumer](examples/downstream/Consumer.lean) exercise the public surface.

Use the bounded [development and verification route](doc/DEVELOPMENT.md). CI includes builds, tests, linters, style, axiom audits, controls, inventory and downstream build/audit; the extra independent library and client kernel replays run locally before publication. Incremental caches preserve unaffected outputs across package-version bumps and do not replace current verification.

The package pins Lean **4.34.1** and Mathlib **`d13f23b723b8a846827a245b89c10fc7d3f11612`**. Its extraction source basis is R5Lab **`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`** and the authoritative local Quillen release **`189a8e779f0c68b2dfc6f8195daebb3e684a5905`**. The initial 133 selected Quillen files from **`83629578a3d70787d41ec631f5234af8758716af`** are byte-identical in that release. See [documentation](doc/README.md), [scope](doc/SCOPE.md), [overall design principles](doc/ARCHITECTURE.md), [naming conventions](doc/NAMING.md), [development commands](doc/DEVELOPMENT.md) and [source provenance](doc/REFERENCES.md). [WORK_PLAN.md](doc/WORK_PLAN.md) records current integration coverage.

Curve/P1/genus/degree/Riemann–Roch and K/G/Q/S applications remain in their original packages. Ordinary Picard groups here give no Picard scheme or curve-degree theorem.
