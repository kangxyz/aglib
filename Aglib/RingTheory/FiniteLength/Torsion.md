# Finite torsion modules in dimension at most one

`Module.finiteLength_of_isTorsion` proves finite length for a finite module over
a Noetherian ring of Krull dimension at most one. Its torsion predicate is
Mathlib's `Module.IsTorsion R M`: each element is killed by a non-zero-divisor
of the original ring. The ring may have several minimal primes and need not
be local or reduced.

Finite generation gives one non-zero-divisor in the module annihilator by
multiplying annihilators of a finite generating set. Every prime in the
module support contains that element. A minimal prime contains no
non-zero-divisor, so each support prime is nonminimal. In dimension at most
one it is therefore maximal. The existing
`Module.finiteLength_of_support_maximal` completes the proof.

The current consumer is `IntegralClosure/Colength.lean`, whose canonical
normalization quotient is torsion by clearing its actual denominators.
Finite generation remains necessary; this result does not assert finite
length for an arbitrary torsion module.
