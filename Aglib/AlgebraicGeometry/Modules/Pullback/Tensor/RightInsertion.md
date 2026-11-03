# Original right insertion and coefficient change

`pullback_rightInsertion` is the original complete unit/tensor comparison law,
moved unchanged from `IntegralTrace/PositiveSectionPullback`. Its public name,
full telescope, proof and two existing declaration-local options are preserved
once. The old module imports this lower owner; its other public laws are unchanged.

`rightInsertion_pullback_transport` takes arbitrary modules on the original
source and target schemes, arbitrary arrows `c` and `d`, original sections, and
the genuine section equation `s' ≫ d = pullbackUnitIso.inv ≫ pullback.map s`.
It proves the complete insertion equation through the same tensor map and
pullback comparison. Neither arrow is inverted. No line, QC, flatness,
finiteness, new instance, alternative category or additional option is used.

The proof combines native tensor composition and inverse-right-unitor
naturality with the original pulled-insertion law. All Hom carriers in its
finite calculation are the original Scheme.Modules carriers. The current
consumer is the actual local raw one-pole transport: its section equation is
supplied by the proved original ideal/dual comparison, not by a desired raw
unit or global one-pole square.

Current source `a10c486c` passed its normal whole-owner check in own191
(5.5-second leaf, 9.1200-second receipt, 2689 jobs, exit 0, no aggregate guard).
This validates the moved insertion law and complete arbitrary-module
coefficient-change equation. The changed old PositiveSectionPullback owner
`e8ba9538` subsequently passed its own whole check in own194 (4.5-second leaf,
8.0661-second receipt, exit 0); this is separate consumer evidence, not a
transfer from the lower check. Higher geometric transport remains unaccepted.
There is no global one-pole, regular-neighbourhood, trace-normalization,
uniform-scalar or H1-vanishing conclusion from this lower pass.
