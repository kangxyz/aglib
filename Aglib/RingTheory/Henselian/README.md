# Quadratic roots in Henselian local rings

`Quadratic` constructs `HenselianLocalRing.of_isAdicComplete` from actual
maximal-ideal adic completeness. Its quadratic-root theorem uses a unit linear
coefficient and a constant coefficient in the maximal ideal; it produces a
root in that ideal without inverting the leading coefficient.

The same leaf proves `IsLocalRing.isUnit_add_of_mem_maximalIdeal`, which
requires locality, a unit and a maximal-ideal summand. The general completion
and finite-target lifting providers remain in the existing completion and
smooth families.

[Finite-algebra idempotents](FiniteAlgebraIdempotents.md) lifts each prescribed
idempotent modulo the extended maximal ideal in any finite commutative algebra
over a Henselian local ring. It retains the actual quotient map and requires
no Noetherianity, flatness, étaleness or completeness.
