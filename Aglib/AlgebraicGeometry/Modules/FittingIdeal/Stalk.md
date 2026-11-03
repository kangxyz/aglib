# Fitting ideals at the original stalk

For a finitely presented module sheaf `M` on an arbitrary scheme `X`,
`fittingIdealSheaf_stalkIdeal` identifies the stalk ideal of `Fitt_k(M)`
with `Module.fittingIdeal` of the actual module stalk, over its original
local ring and with its original scalar action.

The proof applies the existing section-pullback Fitting formula to
`X.fromSpecStalk x`. The native `stalkFromSpecStalkSectionsIso` identifies
the resulting sections with the original stalk. The canonical
`ΓSpecIso` and `fromSpecStalk_app` normalize the scalar map to the original
germ. No alternate stalk comparison is constructed.

Finite presentation is explicit because it supplies the currently available
finite-type pullback result. No Noetherian, reducedness, characteristic,
dimension or freeness assumption is imposed. The immediate consumer is the
stalk-frame criterion for locally rank-one sheaves.
