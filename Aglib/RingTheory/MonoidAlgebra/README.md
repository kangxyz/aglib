# Finite-type monoid algebras

[FiniteType](FiniteType.lean), imported as `Aglib.RingTheory.MonoidAlgebra.FiniteType`, exports `MonoidAlgebra.monoidAlgebra_finiteType` and `monoidAlgebra_isNoetherianRing`. A finitely generated commutative monoid has a finite-type monoid algebra over any commutative coefficient ring; a Noetherian coefficient ring then gives a Noetherian monoid algebra.

The object is the native monoid algebra. Finitely generated monoid and coefficient-ring conditions remain explicit. This is a public general algebra prerequisite, without introducing a Laurent/cycle application object.

[FiniteDominantPrimes](FiniteDominantPrimes.lean) owns the shared
`MonoidAlgebra.FiniteDominantPrime` carrier. The operator-support consumer is
[CommutingAutomorphisms](../../Algebra/Module/CommutingAutomorphisms/README.md);
nonzero multiplicities occur among actual minimal support primes, and the
Noetherian finiteness argument is separate from the `ENat.toNat` definition.
