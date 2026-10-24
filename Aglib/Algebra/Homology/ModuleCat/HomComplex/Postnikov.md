# Residue morphisms and the original derived evaluation

[Postnikov.lean](Postnikov.lean) supplies the algebraic nonzero-morphism
argument used by the surface Grauert–Riemenschneider proof. It uses the
actual A-derived dual and signed evaluation from [Derived.lean](Derived.lean).
All arrows remain in the derived category of A-modules before any scalar
restriction.

For a nonzero finite-length module over a commutative local ring A, a simple quotient
and the unique maximal ideal give a surjection to the actual residue field.
For an upper-bounded derived object, the native top-homology projection then
gives a nonzero map to the residue single whenever that top homology is nonzero.
The top-homology comparison is the original `homToSingleAddEquiv`.

For any morphism alpha : K → E, naturality of the original evaluation gives

    alpha ≫ evaluation(E) = evaluation(K) ≫ D(D(alpha)).

If evaluation(E) is invertible, D(alpha)=0 forces alpha=0. This detection
requires no invertibility statement at D(K). Given an actual isomorphism
rho : D(E) ≅ E and invertibility of evaluation(K), a nonzero alpha : D(K) → E
gives the nonzero A-derived arrow

    rho.inv ≫ D(alpha) ≫ inv(evaluation(K)) : E → K.

`isZero_dual_topHomology_of_residue_vanishing` combines these constructions.
Its explicit inputs are an upper homology bound on D(K), finite length of
that top homology, the actual dual comparison for the same-degree residue
single, invertibility of the two original evaluations, and vanishing of the
actual residue-single morphisms to K. It proves that original top homology
zero. The surface consumer uses n=1 and K=RΓ(X,O_X).

The finite-projective model constructors, intrinsic coinduced residue line,
original geometric residue vanishing, and canonical-module/Serre comparison
must establish those inputs in the surface application. This module neither
assumes a surface-duality structure nor proves full GR from cohomology groups
alone. The potentially nonsplit Postnikov extension is preserved.

The general detection statement keeps the module-carrier and derived-size
universes independent. The finite-length residue specialization uses modules
in the local ring's universe, matching its genuine simple-quotient supplier.

The integrated geometric Grauert–Riemenschneider argument remains open.
The conditional algebraic theorem retains every model, finiteness,
evaluation and residue-vanishing input displayed above.
