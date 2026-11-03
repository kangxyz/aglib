# Finite normalization from a reduced completion

`integralClosure.finite_of_isReduced_completion R hred K`
proves that the literal `integralClosure R K` is finite over R when
R is a Noetherian local ring, its actual
maximal-adic completion is reduced, and K is its supplied total quotient
ring. The original `Algebra R K` and `IsFractionRing R K` are retained;
K may have an independent universe. A domain hypothesis is unnecessary.
For a domain, the conclusion is the N-1 property.

Let S=AdicCompletion (maximalIdeal R) R. Native completion flatness and
the original local completion map make S faithfully flat over R. The
existing completion suppliers give Noetherianity and completeness for
its actual maximal ideal. The supplied hred gives reducedness of S.

The reduced complete-local normalization theorem in
[CompleteLocal](../Nagata/CompleteLocal.lean) therefore
proves finiteness of `integralClosure S (FractionRing S)` over S.
The actual tensor inclusion and faithful-flat finiteness theorem in
[FlatBaseChange](../IntegralClosure/FlatBaseChange.lean) then apply to
the original K and `integralClosure R K`. The upper finiteness and tensor
injection are derived, rather than supplied as hypotheses of this
completion theorem.

The earlier name `finite_of_isReduced_completion_of_dimLE_two` is retained
with the same dimension-free statement. The proof uses the complete-local
finiteness result and faithful-flat descent; no dimension bound is required.

The current consumer is the bounded finite-type surface-chart stability
argument: once that argument proves reducedness of a local ring's
actual completion, this theorem gives finite normalization of that
original local ring. Reduced completion remains an explicit hypothesis;
no arbitrary analytically unramified, finite-type Nagata, or resolution
conclusion is asserted here.
