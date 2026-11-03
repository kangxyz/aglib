# Exact torsion kernel on the original ideal pullback stalk

Source: [StalkKernel.lean](StalkKernel.lean).

For arbitrary schemes, an actual ideal sheaf `I`, a morphism `f : Y → X`
and point `y : Y`, the native pullback/stalk isomorphism followed by the
original `idealModuleStalkEquiv` identifies the full pulled-back stalk with
`O_Y,y ⊗[O_X,f(y)] I_f(y)`. The sole algebra structure is the original
`f.stalkMap y`. The displayed ideal is literally the stalk ideal of
`I.subschemeι.ker`; native `I.ker_subschemeι` identifies it with `I`.

`pullbackIdealToUnit_stalk_square` PROVES that the existing original
`pullbackIdealToUnit` arrow becomes the existing `extendedIdealInclusion`.
The proof retains the native pullback-unit germ, original inclusion and
structure-sheaf germ equation. It does not accept a comparison square as
an additional hypothesis.

If one element of that actual stalk ideal has regular image under
`f.stalkMap y`, `pullbackIdealToUnit_stalk_ker_eq_torsion` identifies its
kernel with the torsion submodule of the literal original source stalk.
`pullbackIdealImage_stalk_ker_eq_torsion` gives the same result for the
existing epi part of `pullbackIdealMonoFactorisation`; it cancels only the
MONO image inclusion, never the full pullback of the original inclusion.

No flatness, domain, finiteness, Noetherianity, normality, local-base or
dimension hypothesis is used. Invertibility of the image and the actual
canonical coefficient are separate downstream geometry.

Direct consumers: [AlgebraicGeometry/Blowup/AffineCenter/StalkKernel](../../Blowup/AffineCenter/StalkKernel.md).
