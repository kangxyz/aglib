# Original quotient-away ring presentation

Source: [Quotient.lean](Quotient.lean).

For an arbitrary commutative ring `R`, ideal `I` and element `t`,
`quotientAwayRingEquiv I t` identifies `R_t / I R_t` with `(R/I)_[t]`.
`quotientAwayRingEquiv_mk` retains the literal native `IsLocalization.Away.map`
on every quotient representative. No Noetherian, regularity or nonzero-ring
condition is introduced.

The implementation uses the native `Ideal.quotEquivOfEq` and
`RingHom.quotientKerEquivOfSurjective` factories on the original map. The
kernel is supplied by `CommRingCat.ker_localizationAway_map`; surjectivity is
the native localized-surjection theorem. These are the same factories and
map used by the original private sheaf-localization argument, which remains
unchanged and does not import this focused public leaf.

The actual consumer is the localized quotient source presentation in
`RightAdjoint.FlatBaseChange.SourcePresentation`. Its scheme and module
comparison laws remain separate from this ring presentation.
