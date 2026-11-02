# Reduced prime-base quotients of regular maps

`Algebra.IsRegularMap.isReduced_quotient_prime` proves reducedness of the
literal quotient `S / pS` for a regular algebra map `R → S` and a prime p of R.
It does not assume the source is a domain, local, or Nagata.

The original map `R/p → κ(p)` is injective. Flatness of S over R preserves
this injection after tensoring, placing `S ⊗[R] (R/p)` inside the regular
residue-field fibre `S ⊗[R] κ(p)`. The native
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot` identifies the source with
`S/pS`. All maps and coefficient actions are the original ones.

This supplies a reduced-quotient input for regularity ascent over localized
DVRs. It does not prove transfer of a regular completion map through a finite
semilocal algebra, nor normality of a completed normalization stalk.

`Algebra.IsRegularMap.isRegularLocalRing_atPrime_of_comap_eq_bot` proves
regularity of the original target localization at a prime over the generic
point of a domain. It uses the existing fraction-base localization and its
`localEquiv`, identifying it with the actual regular tensor fibre through
`IsLocalization.algEquiv`. It does not assert dimension zero of that fibre.
