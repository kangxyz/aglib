# Original affine closed-adjoint homology at a stalk

This module starts from the actual quotient closed immersion
`Spec (R/I) → Spec R`, a quasicoherent ambient coefficient `L`, its supplied
injective resolution `J`, and an actual point `x` of the quotient spectrum.
It compares the homology stalk of the original closed-adjoint image of `J`
with native `Ext` over the actual ambient stalk. The source is the actual
quotient stalk, with scalars through the original closed-immersion stalk map.
Its declarations are in `AlgebraicGeometry.Scheme.Modules.FiniteSourceStalk`.

The construction uses the finite-source tilde counit comparison, the
existing affine Ext comparison and the original exact scalar-extension map.
Both the source quotient and coefficient are identified by their original
germ maps. The public germ law retains the inverse source isomorphism and
forward coefficient isomorphism around that same Ext map.

The raw coefficient map from sections to the actual stalk and its germ
formula apply to every ambient module sheaf. Quasicoherence is required
for their localization property and the resulting scalar-extension
isomorphism. The isomorphism's unit formula is stated directly on the
native tensor `1 ⊗ s`, retaining the original scalar-extension unit.

The two maps from original section homology are localizations at the
complement of the ambient prime. Their unique localization equivalence is
extended to the actual ambient-stalk scalars. The actual scalar square is
`AlgebraicGeometry.stalkMap_toStalk`; no equality of unrelated module actions
is assumed. Native `Ext.{u}` scalar restriction is normalized explicitly
through its original coefficient-scalar action.

The final vanishing theorem uses the proved normal-quotient Ext theorem for
arbitrary finite ambient dimension `d` and target dimension `r ≤ 2`. Its
coefficient frame is an actual isomorphism of the original ambient
coefficient stalk with the ambient local ring. It is a geometric coefficient
input, not a concentration or duality premise. The comparison itself needs
no such frame, normality or regularity.

The current consumer must still transport this affine quotient model through
the actual projective chart and original derived open-adjoint comparison.
The actual top-differential frame must supply the coefficient frame there.
Generic nonvanishing, support, global concentration, codimension and trace
remain separate assemblies. Negative degrees use the existing original
nonnegative-resolution theorem in the lower finite-source module.

The local argument corresponds to the arbitrary-ambient-dimension part of
the chosen-embedding concentration source packet, SHA-256
`e9dd8fb58ebc9cc80e327b39767491af71e5e7292902c3e1f0c388874fcd521f`.
The lower [finite-source calculation](../FiniteSource.md) supplies its
original tilde and section-homology comparisons.
