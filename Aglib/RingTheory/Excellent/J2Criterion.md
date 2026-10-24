# J-2 for semilocal Nagata rings of dimension at most two

`IsJ0Ring.of_injective_finiteType` proves [Stacks Lemma 15.48.4,
tag 07PA](https://stacks.math.columbia.edu/tag/07PA), for the original injective
finite-type algebra map between domains. The source is Noetherian and the
target is J-0. Source and target universes are independent.

Choose a nonzero target element whose away localization is regular. Generic
flatness gives a further nonzero away localization that is flat over the
original source. The resulting map is finitely presented, so its image on
spectra is open. Its domain remains nonzero, making that image nonempty.
For each point of the image, the actual local ring map is flat and local with
regular target. Flat local descent therefore makes the source localization
regular. This constructs the required regular open subset.

The file also exports the pointwise descent and the nonempty open-image
statement used in that proof. It does not assume a regular-locus openness
theorem for either source in order to obtain the conclusion.

`IsNagataRing.isJ0Ring_integralClosure_quotient` constructs the J-0 property for
the literal normalization of each actual prime quotient in any finite extension
of its canonical fraction field. The base is semilocal, Nagata, and of dimension
at most two. Japanese finiteness makes the normalization Noetherian and
semilocal, native normality and integral incomparability give a normal domain of
dimension at most two, and `RegularLocus` supplies J-0. All rings and fields in
this theorem lie in one universe and the Nagata auxiliary test universe is zero.
This supplies the normal-model portion of condition (4); the chosen field and
its original quotient-ring action are retained.

The Noetherian topological supplier
`PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_generic_basicOpen`
proves openness from a relative basic-open neighbourhood in the closure of
each point of the set. The proof uses induction on closed subsets to obtain
constructibility, then generalization stability. Its regular-locus
specialization is the topological step of Stacks 07P8. The algebraic spreading
needed to discharge its premise is proved in the same file: a finite colon
ideal supplies each multiplication kernel, and a finite ideal comparison
spreads generation of the prime ideal. Both conditions are imposed after one
common localization. Iterating regular principal-quotient lifting then proves
`PrimeSpectrum.isOpen_regularLocus_of_isJ0Ring_quotients`, the corrected Stacks
07P9 criterion.

`isJ2Ring_of_isJ0Ring_finiteType_domains` applies that criterion to every
actual prime quotient of every finite-type test algebra. Its conclusion is
the full `IsJ2Ring.{u, 0}` predicate, conditional only on the J-0 tests for all
finite-type domain algebras. No generic-algebraicity restriction is made.

`IsJ0Ring.of_injective_finiteType_of_separablyGenerated` proves Stacks 07PB for
the supplied original fraction-field maps. Separating generation gives formal
smoothness at the generic point. The proof shrinks the J-0 base, passes to a
standard etale polynomial neighbourhood, and uses actual local-etale maps to
obtain regularity. The original coefficient field need not be perfect.

`J2FiniteModel.isJ0Ring_of_finite_model` assembles these results for the literal
image P of S tensor_R T in a common ambient field. The ring P is finite over S
and finite type over T. Its field closure is the join of the two original
fraction-field images. The exact inclusion into their compositum makes that
compositum a fraction field of P, by expressing each element as a quotient of
elements of P. The T-action agrees with the original T-to-E-to-compositum map.

`IsNagataRing.isJ2Ring_of_semilocal_dimLE_two` completes the assembly using
`Algebra.FinitePureConstants.exists_constants`. It factors each finite-type
domain algebra through its actual kernel quotient, constructs the finite
constant extension in an algebraic closure of its fraction field, and uses
the literal normalization of that quotient as the finite J-0 model.

This is the low-dimensional semilocal application of
[Stacks Lemma 15.48.6, tag 07PC](https://stacks.math.columbia.edu/tag/07PC).
The theorem requires `Finite (MaximalSpectrum R)`, `IsNagataRing.{u, 0} R`, and
`ringKrullDim R ≤ 2`; Noetherianity comes from Nagata. Its conclusion is the
full `IsJ2Ring.{u, 0} R`, with all finite-type test algebras in `Type u`.
No perfectness premise on an original coefficient field, generic-algebraicity
restriction on the test algebras, or assertion about arbitrary Nagata rings
is introduced.
