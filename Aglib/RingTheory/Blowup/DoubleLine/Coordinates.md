# Initial double-line coordinates on the original local ring

`IsLocalRing.exists_original_doubleLine_generators` starts with an actual
three-element generating family of the original maximal ideal and an honest
full canonical cotangent kernel `(L²)`, where L is nonzero and homogeneous of
degree one. It constructs actual t,s,z in that same maximal ideal, proves that
they still generate it, and proves the entire original kernel in the order
s,z,t is `(X₁²)`.

The stock degree-one span theorem selects a nonzero original coefficient.
A stock permutation makes that coefficient the middle one, and normalization
uses only its inverse in the original residue field. The two resulting
coefficients are lifted through the original surjective residue homomorphism;
no coefficient-field section, square root, matrix lift or field extension is
chosen. The existing `otherShift` and original permutation/shift map laws
transport the same canonical polynomial map. Native ideal map/comap laws
transport its entire kernel, and elementary ideal-span identities preserve
the original generating ideal. The existing cone presentation backend is
unchanged and remains the downstream consumer of this normalized kernel.

Obtaining the initial linear-square full kernel is a separate classification
obligation. Nonzero scalar-unit multiples can be removed by the existing
principal-ideal unit lemma; no new coefficient assumption is introduced.
This algebraic normalization does not itself establish the exceptional Hilbert
function, child Gorensteinness, a marked transition, or finite termination.
