# Actual exceptional Hilbert function and original cone kernel

Source: [ExceptionalHilbert.lean](ExceptionalHilbert.lean).

`exceptionalPowerLayerGradingEquiv` compares the already implemented
ideal-power quotient with the actual original Rees homogeneous component.
It extends the original A-linear component map over the surjective residue
map. `exceptionalPowerLayerGradingEquiv_class` gives its literal monomial
formula on each original ideal-power representative.

`exceptionalGradedCohomologyEquiv` composes that same comparison with
`exceptionalPowerTheta` and the structural-field-linear H0/section map.
Thus no replacement graded algebra or coefficient-field section is chosen.

For a normal Noetherian Nagata local domain A of dimension two with universal
normal-modification H1 vanishing, `exceptionalUnit_h0_finrank` and
`exceptionalUnit_h1_subsingleton` compute H0 and H1 of the full exceptional
scheme through its original coefficient isomorphism and zeroth ideal power.

`exceptional_hilbert_of_finiteCartier` additionally requires an actual finite
Cartier divisor on that exceptional curve, an isomorphism of its dual ideal
with the exceptional line, and actual ideal H0 vanishing and H1 dimension
one. It then derives `dim gr_m(A)_r = 2r + 1` for all natural r through the
nonreduced Cartier numerical theorem. These additional inputs are not claimed
to follow from rationality alone: the canonical identification and a genuine
Cartier representative, potentially after field extension, are still needed.

For any actual ordered generating triple, the final
`exceptional_quadratic_presentation_of_finiteCartier` calls the existing
`CaseOne.exists_presentation_of_hilbert`. It returns a nonzero homogeneous
quadratic, the entire original canonical cone kernel, a nonzero original
denominator, and the actual saturated chart exceptional quotient with its
original coefficient and fraction maps. The existing full-kernel algebra is
not reimplemented.

No child completeness, finite-module structure over the initial regular
subring, residue-field identification, ADE classification, canonical
generation, or Gorenstein preservation is assumed to have been proved by
these bridges. Actual chart singularities, cubic nonvanishing, persistent
marking and finite termination remain separate geometric obligations.

Present consumers: [ExceptionalHilbert/FirstPower](ExceptionalHilbert/FirstPower.md), [ExceptionalHilbert/Projective](ExceptionalHilbert/Projective.md).
