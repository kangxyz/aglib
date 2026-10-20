# Finite dependence and open stabilizers

`FiniteStabilizers.lean` constructs the actual absolute-Galois subgroup fixing a
finite set of elements of the chosen algebraic closure. It is open in the Krull
topology. An action whose element depends on such a finite set has an open
stabilizer.

`FiniteCoefficientDependence.lean` proves finite scalar dependence for ordinary
multivariate polynomials and monoid algebras. Its polynomial lemma works for any
commutative semiring. Neither file imports schemes or the algebraic simplex.
The simplex and simplex-Laurent statements from the source remain downstream
adapters with that algebra's owner.
