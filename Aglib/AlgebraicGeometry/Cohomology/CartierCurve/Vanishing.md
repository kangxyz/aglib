# Vanishing along a projective-line filtration

[Vanishing.lean](Vanishing.lean) works with actual `Scheme.Modules` short complexes,
native `Sheaf.H`, and the original quotient maps on global sections.

`pushforward_twist_cohomology_subsingleton` proves vanishing of every positive
cohomology group of `i_* O(m)` for `m >= -1`, where `i` is an affine morphism
from the native projective line to a compact separated scheme. The coefficient
ring may be any commutative ring. The proof uses the sharp native twist theorem
and the original affine-pushforward cohomology comparison.

`filtration_vanishing_and_section_lifts` takes actual short exact sequences

`M(j) -> M(j+1) -> Q(j)`

and actual isomorphisms `Q(j) ≅ i_* O(D-j-1)`. If `H^1(M(0))` vanishes and
`N <= D+1`, it proves `H^1(M(j)) = 0` for every `j <= N` and surjectivity of the
original quotient section map for every `j < N`. Quotient vanishing and all
successor section lifts are conclusions.

The reusable helpers `h1_subsingleton_middle` and
`sections_surjective_of_h1_subsingleton` use the native long exact sequence.
The latter concerns the actual map `S.g.val.app (op top)`.

`finite_family_middle` lifts an actual finite quotient-generator family through
the original section map and joins it to the previous term's generators. The
actual cokernel universal property proves that the combined free map is
epimorphic. `finite_family_of_generatingSections` and `finite_family_of_iso`
retain concrete morphisms from the structure module. `augment_finite_family`
retains an arbitrary prescribed additional family verbatim.

The [projective Cartier construction](../../Surfaces/Contraction/ProjectiveSections.md)
discharges the initial vanishing by Serre vanishing and constructs the exact
Cartier sequences and their quotient comparisons. The lower theorem alone is
a filtration theorem with its displayed sequence inputs.
