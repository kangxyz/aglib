# Norm compatibility for actual DVR fraction fields

`DVR.lean` defines `NormedField.NormCompatible R F` by the exact equality between
the norm's closed unit ball and the image of the supplied ring map. It is an
explicit hypothesis, not an unconditional norm producer. For an actual domain
DVR and its fraction field, it proves unit norm one, positive strictly small
uniformizer norm, and the normalized additive-valuation formulas.

`Nontrivial.lean` delegates the small-unit construction to Mathlib's native
`NontriviallyNormedField.ofNormNeOne`. `DVRNontrivial.lean` applies it to an
actual DVR uniformizer, retaining the given norm unchanged.

`UnramifiedDVR.lean` constructs the target compatibility for the actual spectral
norm on a finite fraction-field extension under the original finite, local,
essential finite type, formally unramified DVR extension and compatible scalar
towers. Integrality gives boundedness; preservation of the actual uniformizer
gives the converse unit-ball inclusion. It also records the exact norm-extension,
completeness, and ultrametric conclusions under their original hypotheses.
