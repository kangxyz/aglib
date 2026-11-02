# Exact torsion kernel for the same nonzero affine ideal

Source: [StalkKernel.lean](StalkKernel.lean).

Import `Aglib.AlgebraicGeometry.Blowup.AffineCenter.StalkKernel`.

Let `A` be a domain, `J` its same nonzero ideal, `Y` an integral scheme and
`f : Y → Spec A` an actual dominant morphism. At every actual point `y`,
the original pullback-to-unit map of `affineCenter A J` has exactly the
torsion submodule of its original source stalk as kernel. The same holds
for the epi part of its existing `pullbackIdealMonoFactorisation`.

The regular element needed by the generic actual-stalk theorem is derived:
a genuine nonzero `c ∈ J` stays nonzero under the native localization map
`StructureSheaf.toStalk A (f y)`, then under the original dominant stalk
map `f.stalkMap y`. The original affine-centre stalk identity proves its
membership in the literal stalk ideal. No kernel or compatibility premise
is supplied by the caller.

There is no Noetherianity, normality, properness, finiteness, local-base or
dimension assumption. This theorem does not assert image invertibility or
construct a canonical sheaf on a new model. The canonical numerator can
be substituted only as the same ideal from its existing chosen embedding;
its original coefficient/sheaf comparison is a separate obligation.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/LocalImage](../../Cohomology/Duality/Projective/Relative/NormalSurface/LocalImage.md).
