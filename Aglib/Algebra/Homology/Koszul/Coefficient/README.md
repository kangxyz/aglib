# Finite Koszul complexes with original module coefficients

[The parent coefficient leaf](../Coefficient.lean) replaces the empty-list
unit by the original module in degree zero. Ring coefficients recover the
same native ring Koszul complex. The column splitting transports regular
scalar multiplication to every term.

[Quotient](Quotient.lean) identifies the literal degreewise quotient with the
Koszul complex on quotient coefficients, through its explicit additive-functor
comparison. [Regular](Regular.lean) identifies the scalar-image quotient with
mathlib's `QuotSMulTop` and proves the native weak-regularity recursion.
These exact comparisons are used by [Resolution](../Resolution.lean).

[Finite](Finite.lean) proves that every term is finite when the original
coefficient module is finite, without Noetherianity. Homology finiteness uses
Noetherianity. The coefficient annihilator kills the original terms and
homology without regularity or Noetherianity. Combined with the ring complex's
native projectivity and finite support, these are the finite projective terms
used in the regular-sequence resolution. No canonical exterior basis or
determinant comparison is asserted here.
