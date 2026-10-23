# Exact coinduction for a projective algebra

[Projective.lean](Projective.lean) makes the existing
`ModuleCat.coextendScalars sigma` exact when the original restricted regular
module of the target ring is projective over the source. The map
`sigma : R →+* A` is retained throughout. Finiteness, locality, dimension,
completeness and duality data are not premises.

`coextendScalars_preservesEpimorphisms_of_projective` lifts an actual
R-linear functional from A through the original surjective coefficient map.
The existing coinduction right adjoint preserves kernels. The resulting
`coextendScalars_preservesHomology_of_projective` and
`coextendScalars_preservesFiniteColimits_of_projective` therefore express
exactness of that same functor. The short-exact-row theorem retains the
original row and coefficient maps. These exactness statements allow rings
without commutativity; the following Ext comparison uses commutative rings.

For an arbitrary A-module M, arbitrary R-module N and natural degree q,
`ModuleCat.coextendScalarsExtEquiv` is the existing exact-adjunction
equivalence

`Ext_R^q(Res M, N) ≃+ Ext_A^q(M, coextendScalars sigma N)`.

Its implementation delegates to `restrictCoextendScalarsAdj.extEquiv`.
The forward map is the original exact coinduction map with the adjunction
unit; the inverse is original restriction followed by the adjunction counit.
The ring universes and Ext sizes are independent. Both module categories
use the common carrier universe already required by the native adjunction.
This comparison concerns arbitrary M; the existing
[Ext.lean](Ext.lean) instead identifies derived coinduction homology with
`Ext_R(A,N)`.

For every `a : A`, `coextendScalarsExtEquiv_source_smul` identifies
precomposition with the restriction of `a • identity_M` with intrinsic
scalar multiplication by a on the A-Ext group. Its inverse form preserves
the same action. This states the actual source-multiplication compatibility
without assigning an A-action to N.

The degree-zero formulas are literal:

* h is sent to `m ↦ (a ↦ h(a • m))`;
* an A-linear map to coinduced coefficients is sent to `m ↦ h(m)(1)`;
* the counit itself is `lambda ↦ lambda(1)`.

In particular, for N equal to the source ring, the coefficient is the
existing coinduced module `Hom_R(A,R)`, whose native action is
`(a • lambda)(b) = lambda(b*a)`. Its construction and action are not replaced.
The composition and counit comparisons in
[Coinduction.lean](../Coinduction.lean) and the installed derived composition
in [Derived.lean](Derived.lean) remain the existing suppliers.

The current consumer is the regular-base surface canonical-module route.
The passed
[finite-normal-algebra theorem](../../../../../RingTheory/RegularLocalRing/FiniteNormalAlgebra.md)
provides projectivity under its finite injective local dimension-two
hypotheses; those assumptions do not enter this general leaf. This file
does not construct a finite regular subring or prove a derived-Hom
identification, biduality, surface concentration, geometric trace
compatibility or Grauert--Riemenschneider vanishing. Finite-length H1 for
proper normal local surface modifications is a separate supplier and does
not by itself provide H0, higher-degree vanishing or Leray statements.

Source basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. Native compilation
is coordinated by the principal; the author retains responsibility for
the coupled proof repair. Existing coinduction files and the passed
finite-normal-algebra pair remain unchanged.
