# Compatible lifting from a smooth reduction

Let R, C, and A be commutative rings with specified R-algebra structures
on C and A. Let I⊂R and J⊂A satisfy I A⊆J. Assume C is flat over R and
the literal quotient map R/I→C/IC is formally smooth. Then every
specified R-algebra map f:C→A/J lifts to an R-algebra map
C→AdicCompletion J A. If A is J-adically complete, it lifts to an actual
map C→A. In both statements the original quotient composite is exactly
f, and the original R-action is retained.

The public interfaces are
`Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq_of_quotient`
and
`Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete_of_quotient`.
Neither C nor A is assumed Noetherian or finite over the base.

For the one-step construction, suppose g:C→A/Jⁿ has already been chosen,
with n≥1. Put Rn=R/Iⁿ⁺¹, Cn=C/Iⁿ⁺¹C, An=A/Jⁿ⁺¹, and Ap=A/Jⁿ. The
inclusions Iⁿ⁺¹A⊆Jⁿ⁺¹⊆Jⁿ supply the actual Rn-algebra structures on An
and Ap. The original R-actions factor through these quotient actions.
The map g kills Iⁿ⁺¹C, so `Ideal.Quotient.liftₐ` gives Cn→Ap.
`AlgHom.extendScalarsOfSurjective` regards this same map and the actual
transition An→Ap as Rn-algebra maps.

The transition is surjective and its kernel Jⁿ/Jⁿ⁺¹ squares to zero.
[`AdicQuotient`](AdicQuotient.lean) supplies formal smoothness of Cn over
Rn from the original flatness and smooth reduction. Native
`Algebra.FormallySmooth.liftOfSurjective` gives Cn→An. Restricting scalars
to R and composing with C→Cn produces g', whose actual transition
composite is g.

The construction chooses these lifts recursively, beginning with f at
n=1 and the unique map at n=0. The one-step equation implies compatibility
for all m≤n by composition of the actual quotient transitions.
`AdicCompletion.liftAlgHom` forms the inverse-limit map. Its evaluation
formula proves the original quotient identity. In the complete-target
case, the construction then composes with the inverse of the actual
completion equivalence.

The current consumer is the map from a constructed Cohen DVR C to a
complete mixed-characteristic local ring A. Taking R=Z, I=(p), and J the
maximal ideal of A gives that map once the actual Cohen residue marking
and prime-field action discharge the smooth-reduction premise. The
arbitrary-residue Cohen-ring construction remains separate; this module
does not supply its existence as a premise to the full finite regular
subring theorem.

The square-zero smoothness criterion is
[Stacks Project, Tag 031L](https://stacks.math.columbia.edu/tag/031L),
through the native supplier used in `AdicQuotient`. The compatible lifting
uses the native infinitesimal lifting property in
`Mathlib/RingTheory/Smooth/Basic.lean` and the original adic completion
maps in `Mathlib/RingTheory/AdicCompletion/Algebra.lean`.

Source basis: Aglib HEAD `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Lean 4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
