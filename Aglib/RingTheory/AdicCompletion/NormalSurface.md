# Normal completions of actual surface charts

[NormalSurface.lean](NormalSurface.lean) treats an injective local map
`A → B` between local domains of dimension two. The original `A` is
complete, the canonical residue extension is finite, and the original `B`
is Noetherian, normal and Nagata. Normality or domainhood of the completion is
not assumed. The completion is the identical native maximal-adic
`AdicCompletion (maximalIdeal B) B`.

`isReduced_primeQuotient_of_nagata_surface` uses the original Nagata quotient
and `quotientEquivPrimeCompletion`; these reducedness statements require
a local Nagata base of dimension at most two, without a separate domain
assumption on that base. It also gives reducedness of each actual
ordinary formal fibre. It does not assert geometric regularity.

At each nonmaximal prime of the completion, the new formal-fibre dimension
lemma and the existing associated-DVR ascent theorem give regularity of the
original local ring. The native regular parameter pair of `B` stays regular
after flat completion. Its two equations exclude the maximal ideal from the
associated primes of every regular principal quotient. Thus an integral total
fraction can be tested at its associated primes, where the local rings are
normal; clearing the original denominators proves integral closedness.

This associated-prime implementation is the same regular-pair obstruction
as the paper's conductor argument, with no separate powered-parameter or
finite-support module construction. Both cancellation equations are proved
inside the helper; no abstract normal-ascent premise is introduced.

`normalDomain_of_complete_normal_surface` returns both `IsDomain` and
`IsIntegrallyClosed` on the identical native maximal-adic completion. To prove
the first property, it realizes the ordinary generic fibre as a localization,
uses its zero-dimensionality and reducedness to obtain an Artinian total
quotient ring, and descends idempotents through the proved integral closedness.
The original completion is local, so only one field factor can remain.

The argument corresponds to Section 4 of the R.F1c complete-base source
packet, revision 2, SHA-256
`9a953be7a5616a242d86dfeb0fe7ab02183196e5e8efc0c84f0e61e1334a38fe`.
[SurfaceFormalFiber](SurfaceFormalFiber.md) supplies the lower formal-fibre
dimension theorem. [MarkedPath](../../AlgebraicGeometry/Blowup/Arc/MarkedPath.md)
uses this normal-domain completion conclusion under its actual original
scalar-map hypotheses. No general resolution theorem is concluded here.
