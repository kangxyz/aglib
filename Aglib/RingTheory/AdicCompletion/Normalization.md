# Finite normalization from a reduced completion

`integralClosure.finite_of_isReduced_completion_of_dimLE_two R hred K`
proves that the literal `integralClosure R K` is finite over R when
R is a Noetherian local ring of dimension at most two, its actual
maximal-adic completion is reduced, and K is its supplied total quotient
ring. The original `Algebra R K` and `IsFractionRing R K` are retained;
K may have an independent universe. A domain hypothesis is unnecessary.
For a domain, the conclusion is the N-1 property.

Let S=AdicCompletion (maximalIdeal R) R. Native completion flatness and
the original local completion map make S faithfully flat over R. The
existing completion suppliers give Noetherianity and completeness for
its actual maximal ideal. The dimension comparison gives dim(S)≤2,
and the supplied hred gives reducedness of S.

The reduced complete-surface normalization theorem in
[CompleteLocalSurface](../Nagata/CompleteLocalSurface.lean) therefore
proves finiteness of `integralClosure S (FractionRing S)` over S.
The actual tensor inclusion and faithful-flat finiteness theorem in
[FlatBaseChange](../IntegralClosure/FlatBaseChange.lean) then apply to
the original K and `integralClosure R K`. The upper finiteness and tensor
injection are derived, rather than supplied as hypotheses of this
completion theorem.

This is the dimension-at-most-two version of
[Stacks, Lemma 10.162.10 (032Y), parts (4) and (5)](https://stacks.math.columbia.edu/tag/032Y). The source's complete-domain
finiteness input is supplied here by the proved CN2/CR2 results within
the same dimension bound.

The current consumer is the bounded finite-type surface-chart stability
argument: once that argument proves reducedness of a local ring's
actual completion, this theorem gives finite normalization of that
original local ring. Reduced completion remains an explicit hypothesis;
no arbitrary analytically unramified, finite-type Nagata, or resolution
conclusion is asserted here.
