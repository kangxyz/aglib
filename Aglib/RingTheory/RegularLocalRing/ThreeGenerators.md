# Cotangent rank from three actual generators

`IsLocalRing.cotangent_finrank_eq_three_of_spanFinrank_le_three` works on an
arbitrary commutative Noetherian local ring of dimension two. Nonregularity
and an actual maximal-ideal generator bound of three force its cotangent
dimension over the original residue field to equal three.

The native regularity criterion excludes a bound of two. The existing
maximal-ideal span-rank/cotangent-rank equality then gives the conclusion.
No associated-graded Hilbert function or kernel is used.

`IsLocalRing.cotangent_finrank_eq_three_of_maximalIdeal_span_triple` supplies
the generator bound from the literal equality `m = span {p,u,v}`. The three
elements need not be separately assumed distinct or minimal. Neither theorem
assumes the ring is a domain, normal, Gorenstein or rational.

The surface-resolution consumers in both quadratic cases first construct
these actual child generators independently of the child Hilbert function.
The shared rank theorem then feeds the ordinary exceptional first-power
numerics; it does not by itself identify the entire quadratic kernel.
