# Coefficient canonical twist H1 vanishing

The primary endpoint is
`cmCurveCoefficientTwist_h1_subsingleton_of_generated_nontrivial`:
on the actual projective CM curve over any field, with its genuine finite
rank-one coefficient V, suppose the original structural H0 map is bijective,
L is an invertible line whose original global-section evaluation is epic,
and L is not isomorphic to the structure module. Then original
H1(L tensor omega_(C,V)) vanishes.

The proof uses no algebraic closure or regular hyperplane. Global generation
and scalar constants show every morphism L → O is zero: a nonzero composite
with a generating section is a nonzero scalar endomorphism of O, so is
invertible. Then L → O is epic and hence an isomorphism by equal rank,
contradicting nontriviality. The original dual-tensor adjunction gives
Ext1(O,L tensor omega) = Ext1(L^-1,omega), and the original coefficient
Serre equivalence identifies the latter with Hom_k(H0(L^-1),V). The preceding
vanishing kills this group without orienting V. This is the arbitrary-field
argument in Stacks [0B62](https://stacks.math.columbia.edu/tag/0B62), with
all tensor and Ext comparisons retained.

For the full exceptional curve, it remains necessary to derive original
structural H0, global generation and nontriviality for every positive power
of the actual exceptional ideal line. The theorem does not replace these
with conclusions packaged as geometric data. Global generation of
omega tensor L remains a different endpoint with an actual degree-at-least-two
input (Stacks [0B5H](https://stacks.math.columbia.edu/tag/0B5H)).

## Independent section-row route

`cmCurveCoefficientEnlargement_h1_subsingleton` treats the actual mono
`a : omega_(C,V) → F` on the actual projective CM curve. Besides the coefficient
Serre premises, it assumes the original structural H0 map is bijective,
F is coherent, the actual cokernel has finite closed support and is nonzero,
and F has no nonzero coherent finite-closed-support subobject.

If H1(F) were nonzero, original trace-normalized Serre duality would split
the same cokernel row. The section of its quotient arrow would embed the
nonzero finite-support cokernel in F, contradicting purity. Therefore the
original H1(F) is zero. The proof retains the coefficient line throughout.
This is the finite-support enlargement argument of Stacks
[0B5E](https://stacks.math.columbia.edu/tag/0B5E).

`cmCurveCoefficientTwist_h1_subsingleton` specializes this route to
F = L tensor omega_(C,V) and derives purity from the actual dual-tensor
equivalence. Its consumer must still construct the original mono from a
regular section and prove finite nonempty quotient. No positive-twist endpoint or exceptional-curve application
is claimed before those premises are derived from its actual geometry.

Native status: authored for the principal's incremental batch; no successful
compilation, lint, test or axiom-audit coverage is asserted yet.
