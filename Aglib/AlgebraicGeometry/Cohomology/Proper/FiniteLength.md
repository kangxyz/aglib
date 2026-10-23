# Finite-length positive proper cohomology

`Scheme.localPuncturedSpectrum R` is the literal open complement of
`IsLocalRing.closedPoint R` in `Spec R`.

`Scheme.Cohomology.moduleCohomology_isFiniteLength_of_proper_of_isIso_puncturedSpectrum`
states that a coherent module sheaf on a proper scheme over a Noetherian local
ring has finite-length cohomology in every positive degree if the original
morphism restricts to an isomorphism over this punctured spectrum. The result
uses the original additive-sheaf `Sheaf.H` and the original structural action
`moduleCohomologyModuleOfHom` induced by `f.appTop` and `ΓSpecIso`.

Proper coherent cohomology is finite. For each nonclosed prime `p`, the actual
map `Spec R_p → Spec R` lands in the punctured spectrum, and its actual
base change is an isomorphism. The base-changed source is affine. Flat base
change for separated quasi-compact morphisms and affine quasicoherent
acyclicity therefore annihilate `R_p ⊗_R H^q(X, M)` for `q > 0`.
The native localization–tensor equivalence identifies this with localization
of the original cohomology module. Its support is contained in the closed
point, so finite-length detection applies.

The coefficient need not be relatively flat. No fibrewise-vanishing oracle,
finite-length premise, source regularity, or restriction on the local ring's
dimension is used.
