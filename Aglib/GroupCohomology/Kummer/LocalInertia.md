# Kummer root ratios over inertia-fixed local fields

`LocalInertia.lean` uses `GroupCohomology.Kummer.LocalInertia` and preserves the source family's actual maps.

Let L be an actual intermediate field of AlgebraicClosure K, where K has characteristic zero
and is the fraction field of the DVR R. The supplied absolute prime Q is maximal above the
maximal ideal of R. Original inertia is independently required to fix every element of L. At a
positive level invertible in R, roots of units in the localization of integralClosure R L at
the contraction of Q are fixed by inertia. The root-ratio formula additionally requires this
localization to be a DVR with fraction field L and the image of the same R-uniformizer to be
irreducible.

Source: `R5Lab.Aglib.GroupCohomology.Kummer.LocalInertia`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`c154d443e1813a301c45c799ce77024510d0af412fee288335c8ae04818b765a`.

This correspondence records source identity and conditions. Compilation and final
package checks have their own scoped evidence; no downstream geometric realization
is asserted by this migration.
