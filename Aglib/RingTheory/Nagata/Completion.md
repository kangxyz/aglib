# Reduced completions of Nagata local domains in dimensions at most two

Import `Aglib.RingTheory.Nagata.Completion`.

`IsNagataRing.isReduced_completion_of_dimLE_one` and
`IsNagataRing.isReduced_completion_of_dimLE_two` give reducedness of the
actual maximal-ideal completion of a local domain R of Krull dimension
at most one and at most two, respectively. Both use the existing
`IsNagataRing.{u, 0} R` for `R : Type u`; Noetherianity comes from that
predicate. They require no normality, completeness, regularity,
separability, or characteristic assumption on R.

All rings and tested extension fields remain in the same ambient
universe u, with auxiliary Japanese test universe zero. No change of
test universe or universe-invariance theorem is used.

The construction has a finite acyclic order.

1. A field has zero maximal ideal, and its zero-adic completion is
   identified with the original field by `AdicCompletion.ofAlgEquiv`.
2. A normal Noetherian local domain of dimension at most one is a field
   or a DVR. The [dimension-one criterion](../DiscreteValuationRing/DimensionOne.md)
   supplies the DVR structure in the second case. The existing
   [completed-DVR theorem](../AdicCompletion/DiscreteValuationRing.lean)
   then makes its actual completion a domain, hence reduced.
3. For a local Nagata domain R of dimension at most one, form the literal
   normalization `C = integralClosure R (FractionRing R)`. The Japanese
   condition of R supplies finiteness of C using the identity finite
   fraction-field extension. Integral-closure normality supplies
   normality of C. The original R -> C map is injective because its
   composite with the inclusion into FractionRing R is the original
   fraction-field map. Each actual maximal localization of C satisfies
   step 2. The [finite-completion descent theorem](../AdicCompletion/FiniteReducedDescent.md)
   therefore gives reducedness of the original completion of R.
4. For a normal local Nagata domain R of dimension at most two, first
   handle the field case. Otherwise choose a nonzero x in its maximal
   ideal. The ambient localizations at associated primes p of R/(x) are
   DVRs by the dimension-one associated-principal theorem. Every actual
   quotient R/p is Nagata by [finite quotient stability](Finite.md).
   The quotient kills the original nonzerodivisor x, so its dimension is
   at most one. Step 3 gives reducedness of its actual maximal-ideal
   completion. These are precisely the DVR and reduced-prime-completion
   inputs of the [associated-prime criterion](../AdicCompletion/AssociatedPrimeCriterion.md),
   which yields reducedness of the completion of R.
5. For general R of dimension at most two, use the same literal finite
   normalization C. [Finite ascent](Finite.md) and
   [localization stability](Localization.md) make its actual normal local
   branches Nagata. Step 4 applies to each branch. Finite-completion
   descent then gives reducedness of the original completion of R.

The dimension estimate for C uses integral incomparability. The actual
prime contraction map is strictly monotone along chains by
`Ideal.IsIntegral.under_lt_under`; `Order.krullDim_le_of_strictMono`
therefore gives dim(C) <= dim(R). Each localization has dimension equal
to the height of its actual prime, bounded by dim(C). This argument
applies to the possibly nonnormal initial R and needs no normal-base
going-down theorem.

The normal local and finite normal-model arguments are first proved
with abstract model rings, retaining their original algebra maps. Only
then are they specialized to the literal integral closure. Quotient
locality is obtained from the original surjective quotient map. The
associated-prime consumer uses the already constructed comparison with
the completion of that same quotient.

These theorems supply the bounded Nagata-to-reduced-completion direction
used by the surface normalization route. They do not import
`Nagata.CompleteSurface`, the separate F2/CN2 finiteness argument, or
finite-type Nagata stability.
[AdicCompletion.Normalization](../AdicCompletion/Normalization.md) supplies
the reverse implication from reduced completion to finite normalization
in the same dimension bound. [Polynomial](Polynomial.md) supplies
polynomial Japanese stability, and [FiniteTypeSurface](FiniteTypeSurface.md)
uses rational adjunction for the actual generically finite surface charts.
Those are separate interfaces with their stated hypotheses.
