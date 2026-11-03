# Concatenation of normalized point-blowup chains

Source: [ChainComposition.lean](ChainComposition.lean).

For `c : NormalizedPointBlowupChain f` and
`d : NormalizedPointBlowupChain g`, `c.comp d` is indexed by the literal
composite `g ≫ f`. It retains the original closed nongeneric centres and
normalized blowup arrows.

`length_comp` proves `(c.comp d).length = c.length + d.length`.
The equality transports arise only from identity and associativity of those
arrows. This operation combines supplied or constructed chains; it adds no
properness, regularity or existence assertion.

Present consumers: [Comparison](Comparison.md).
