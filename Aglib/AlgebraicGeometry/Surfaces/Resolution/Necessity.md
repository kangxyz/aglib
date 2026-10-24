# Necessity in the absolute surface resolution criterion

`Hom.normalization_conditions_of_proper_birational_regular` starts with
an integral Noetherian Y of topological Krull dimension at most two and
an actual proper dominant map f:X→Y from an integral scheme with regular
stalks. Birationality is invertibility of the original `functionFieldMap f`.
For the literal generic inclusion γ:Y.functionField→Y, it proves:

- γ.fromNormalization is finite;
- the set of nonregular points of γ.normalization is finite;
- the maximal-ideal completion of every actual normalization stalk is an
  integrally closed domain.

Thus it gives the necessity implication RES(1)⇒RES(2), with the stronger
completion conclusion at every normalization point. It constructs no
resolution and assumes no Nagata, excellence, J-2, Grauert–Riemenschneider,
field or trait presentation, absolute separatedness, or structural-section
bijection.

## Literal normalization and finite singular set

Regular local rings are normal domains, so the supplied regular model
has normal stalks. `genericNormalization_isFinite_of_proper_birational`
then proves finiteness of the literal normalization from the original
finite section algebra and its original coefficient action. The actual
`genericNormalizationLift` provides the factor X→N, with its original
triangle, properness, dominance and function-field isomorphism.

Finiteness over Noetherian Y makes N Noetherian. For an affine target open
U, its inverse image is affine with a finite section algebra. Integral
incomparability makes the original map on prime spectra strictly
monotone and therefore bounds the latter algebra's Krull dimension by
that of Γ(Y,U). The open embedding Spec Γ(Y,U)→Y bounds this by dim(Y).
The actual normalization stalk is a localization of its affine section
ring, so every such stalk has dimension at most two. This uses no
catenary dimension formula.

The existing target isomorphism locus of X→N has finite closed complement.
Its actual restriction is an isomorphism. The inverse restriction followed
by the original source-open inclusion pulls regularity from X to that
open of N. Every singular point of N is therefore in the finite complement.
No openness theorem for the regular locus is assumed.

## Original local sections and completion

Fix y∈N and B=O_(N,y). Form the literal pullback P=X×_N Spec B with its
original projections a:P→X and p:P→Spec B. The canonical Spec B→N is flat
and a preimmersion. Its base change a has isomorphic original stalk maps,
so regularity of X gives regularity of P.

Proper birationality onto normal N makes the original structure-sheaf
map O_N→g_*O_X an isomorphism. Choose an affine neighbourhood U of y.
The inverse image of U in Spec B is all of Spec B. Native flat base change
of sections on this actual pullback gives the ring pushout

    Γ(N,U)  →  Γ(X,g⁻¹U)
      ↓              ↓
    Γ(Spec B,⊤) → Γ(P,⊤).

The top map is the original component of the structure-sheaf isomorphism.
Its pushout, the bottom original p.appTop, is consequently an isomorphism.
Composing with the original ΓSpecIso inverse proves bijectivity of the
literal `LocalRing.properStructuralSectionsMap p`. No fraction-field map
for the localized source and no abstract section-module equivalence is
introduced.

`Hom.completion_normal_at_of_proper_birational_regular` supplies this local
argument for any normal locally Noetherian integral target, without a
surface-dimension restriction. It feeds the derived literal bijection and
regularity into `completion_normal_of_proper_regular_structuralSections`.
That provider uses the original completed flat H0 map, proves regularity
of the completed pullback, and proves its connectedness and integrality
before transferring normal domain structure through the original completed
structural map. The final necessity theorem applies it to each point of N.

This is the direct proper-birational necessity argument. Finiteness of the normalization, dimension, the singular
set bound, regularity of the local source and the structural bijection are
all derived within the displayed hypotheses.
