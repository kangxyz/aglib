# Aglib

Aglib is a Lean 4 library for commutative algebra, arbitrary-dimensional scheme geometry, module sheaves and Zariski cohomology, built on Mathlib. It works with Mathlib's actual rings, schemes, module sheaves and `Sheaf.H`, extending their native namespaces with reusable constructions, canonical maps and theorems.

The library develops general theory. Curve, projective-line, genus, degree, Riemann–Roch and K/G/Q/S applications remain downstream.

## Installation and use

Use Lean **4.34.1**. Add Aglib to your project's `lakefile.toml`:

```toml
[[require]]
name = "Aglib"
git = "https://github.com/kangxyz/aglib.git"
rev = "main"
```

Run `lake update` to resolve the dependency. Aglib pins its compatible Mathlib revision in [lakefile.toml](lakefile.toml); retain the resulting `lake-manifest.json` for reproducible builds. Use a specific Aglib commit in place of `main` when you need a fixed version.

Import a focused module, for example to use the domain theorem for tensor products over an algebraically closed field:

```lean
import Aglib.RingTheory.TensorProduct.Domain

open scoped TensorProduct

example (k A B : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [IsDomain A] [Algebra k A]
    [CommRing B] [IsDomain B] [Algebra k B] :
    IsDomain (A ⊗[k] B) :=
  Algebra.TensorProduct.tensorProduct_isDomain k A B
```

The theorem is [defined here](Aglib/RingTheory/TensorProduct/Domain.lean). Use `import Aglib` for the aggregate public surface. [Interface examples](AglibTest) and an [independent downstream package](examples/downstream) show further uses.

## Main results

The linked family guides give precise statements, focused imports and canonical declaration names.

- **Commutative algebra:** [regular local rings](Aglib/RingTheory/RegularLocalRing/README.md) are domains and integrally closed; in positive dimension a scalar-regular first parameter gives a regular quotient of dimension one less. [Tensor products of commutative domains](Aglib/RingTheory/TensorProduct/README.md) over an algebraically closed field are domains, without a finite-type assumption. A [finite module over a Noetherian ring](Aglib/RingTheory/FiniteLength/README.md) has finite length if every prime in its support is maximal.
- **Affine module sheaves and vector bundles:** [quasicoherent sheaves on affine schemes](Aglib/AlgebraicGeometry/Modules/QuasiCoherent/Affine/README.md) have the native module/tilde comparison and vanishing positive Zariski cohomology over every commutative ring. [Finite locally free sheaves](Aglib/AlgebraicGeometry/Modules/LocallyFree/README.md) form an exact category, and arbitrary scheme pullback preserves its short exact sequences by local splitting. On [affine schemes](Aglib/AlgebraicGeometry/Modules/LocallyFree/Affine/README.md), their global sections are finitely presented projective modules with actual finite-free retracts.
- **Geometry and invertible sheaves:** [smooth schemes over arbitrary fields](Aglib/AlgebraicGeometry/Morphisms/Smooth/README.md) have regular and normal stalks; relative dimension `n` bounds stalk dimensions, with equality at closed points and scheme dimension `n` for nonempty schemes. [Locally Noetherian schemes with domain stalks](Aglib/AlgebraicGeometry/Properties/Normal/README.md) have open irreducible components; connectedness together with domain and integrally closed stalks gives integrality. [Rank-one module sheaves](Aglib/AlgebraicGeometry/Modules/Invertible/README.md) give an ordinary additive Picard group on every scheme and additive pullback along every scheme morphism.
- **Canonical comparison maps:** [affine module base change](Aglib/AlgebraicGeometry/Modules/BaseChange/README.md) is invertible for affine morphisms, arbitrary quasicoherent coefficients and arbitrary change of base, without flatness or Noetherianity. [Flat module-cohomology base change](Aglib/AlgebraicGeometry/Cohomology/BaseChange/Modules/README.md) is invertible in every nonnegative degree for a quasi-compact separated morphism to an arbitrary affine base, a flat ring map and arbitrary quasicoherent coefficients. The [projection formula](Aglib/AlgebraicGeometry/Modules/ProjectionFormula/README.md) holds for arbitrary scheme morphisms with finite locally free target coefficient, and for closed immersions with both coefficients arbitrary.
- **Cohomological dimension:** on a [Noetherian scheme of topological Krull dimension at most `d`](Aglib/AlgebraicGeometry/Cohomology/Vanishing/README.md), every abelian sheaf has zero Zariski `Sheaf.H` in degrees greater than `d`; properness and quasicoherence are unnecessary.
- **Complexes and derived methods:** [Godement totalization](Aglib/AlgebraicGeometry/Cohomology/Godement/TotalComplex/README.md) preserves categorical short exactness even on unbounded integer complexes; augmentation and D+ calculation retain bounded-below or explicit lower-term bounds. [Short exact bounded-below complexes](Aglib/Algebra/Homology/DerivedCategory/Plus/README.md) give distinguished triangles in an abelian derived setting; single-term comparison retains both lower and upper term bounds, and derived contraction gives the stated one-sided unit-compatible isomorphism. [Joint open covers](Aglib/AlgebraicGeometry/Cohomology/Locality/README.md) detect isomorphisms and zero objects in the bounded-below derived module category from the actual local hypotheses. [Affine induction on qcqs schemes](Aglib/AlgebraicGeometry/Properties/README.md) uses isomorphism invariance and compact binary-union closure with the overlap property supplied.

Some interfaces retain explicit general inputs: proper module-cohomology finiteness uses `ProperModuleCohomologyFinite`, smooth differential rank uses `SmoothDifferentialRank`, local-basis fibre/rank comparisons use `LocalBasisFibreDimension`, and relative locally free cohomology base change uses `LocalFreeCohomologyBaseChange`. These premises remain required where used; the derived constructions do not supply them. See the [interface guide](doc/INTERFACES.md).

## Interfaces and documentation

| Family | Interfaces |
| --- | --- |
| [RingTheory](Aglib/RingTheory/README.md) | Descent and equalizers, regular-local parameters, support, filtrations, length and scalar Euler expressions |
| [Algebra](Aglib/Algebra/README.md) | Finite-module functors, localized exactness, mapping cones and total complexes |
| [CategoryTheory](Aglib/CategoryTheory/README.md) | Selected exact structures and functors, abelian subcategories, small models, injective resolutions and site Cech comparisons |
| [Topology/Sheaves](Aglib/Topology/Sheaves/README.md) | Section complexes, basis detection, Mayer–Vietoris and Noetherian-space support |
| [AlgebraicGeometry](Aglib/AlgebraicGeometry/README.md) | Scheme modules, quasicoherence, locally free/coherent/invertible/differential sheaves, morphisms and cohomology |

Finite-type quasicoherent theory is available on arbitrary schemes; the coherent specialization keeps its explicit locally Noetherian guard. Constructions reuse canonical objects and maps rather than introducing parallel replacements.

The [documentation index](doc/README.md) links reading routes, [scope](doc/SCOPE.md), [architecture](doc/ARCHITECTURE.md), [naming](doc/NAMING.md), [source provenance](doc/REFERENCES.md) and [integration status](doc/WORK_PLAN.md).

## Contributing and license

Follow the [development guide](doc/DEVELOPMENT.md) for setup, focused builds, tests, linters and integration checks, and the [contribution conventions](doc/DEVELOPMENT.md#contribution-conventions) for source and documentation changes. [AGENTS.md](AGENTS.md) gives concise instructions for coding agents.

Current source author credit is **kangxyz**; future contributions should credit their actual authors. Aglib is licensed under [Apache 2.0](LICENSE).
