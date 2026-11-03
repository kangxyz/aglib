# Whole right-adjoint coherence for original affine maps

Source: [PushforwardComposition.lean](PushforwardComposition.lean).

`pushforwardGlobalSectionsIso_ringHom_comp_inv` retains arbitrary original
R/S/T, raw f/g and the supplied triangle proof h. For every target sheaf G,
it equates the composite of the original inverse affine section comparisons,
geometric pushforward composition and equality transport with the original
inverse scalar restriction comparison followed by the composite-map section
comparison. No quasicoherence hypothesis occurs.

The proof applies native conjugateEquiv to the accepted complete equality
`tildePullbackIso_ringHom_comp_hom_of_triangle`, normalizes existing conjugate
identities, and takes NatTrans.congr_app. It does not copy the final section
calculation or replace TildePullback, which stays the unique implementation.
The original source locations are injectivity118–121, normalization122–153,
and section calculation154–162; the new corollary uses no element evaluation.

The sole import is the unchanged TildePullback owner. PullbackMates consumes
this complete consequence.
