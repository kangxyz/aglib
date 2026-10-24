# The intrinsic residue line of the coinduced dual

Let R→A be the actual finite local map of commutative local rings, with R
regular local of dimension two. Both rings and the module carriers lie in
one universe. Let I be a K-injective coefficient complex equipped with an
actual quasi-isomorphism R[0]→I, and set J=Hom_R(A,I) by native scalar
coinduction. The A-action on J is its original action on the argument of
each functional.

`residueDualComplex I` is the actual A-module-valued complex
`Hom_A(k_A[0],J)`. Its native homology is `residueDualHomology I n`.
These modules carry their A-actions before any scalar restriction or Ext
comparison.

## Restriction computes the intrinsic length

`coinducedSingleHomologyExtLinearEquiv` restricts this original
A-homology to R and compares it with native `Ext_R^n(k_A,R)`. It uses the
original evaluation-at-one coinduction comparison, native module homology,
the original cocycle-to-derived arrow, and the supplied augmentation of I.
No action is transferred from an abstractly isomorphic module.

The residue extension k_A/k_R is finite because A is finite over R, and its
degree f is positive. The native restriction-length formula says

`length_R(M) = length_A(M) * f`.

In particular, k_A has finite R-length f. The finite-length Ext-two theorem
gives `length_R(H²(Hom_A(k_A[0],J))) = f`. Cancellation by the finite nonzero
f gives A-length one. The classification of simple modules over the local
ring A therefore supplies an A-linear isomorphism from this original
homology module to k_A. This last line identification is a choice.

The public endpoints are `residueDualHomology_length_eq_one` and
`nonempty_residueDualHomology_linearEquiv`. Their proof uses neither a
field trace nor separability or a coefficient field.

## Integer concentration and original normalization

For nonnegative n≠2, native finite-length Ext concentration and the same
original cohomology comparison give zero homology. If I is termwise zero
below degree zero, native coinduction has the same lower bound. The Hom
complex from k_A[0] is then also termwise zero in negative degrees.
`residueDualHomology_isZero_of_ne_two` covers every integer n≠2.

`residueDualComplexSingleIso` identifies Q of the actual Hom complex with
its original A-homology placed in degree two. It uses
`DerivedCategory.isoSingleHomology` and the original
`homologyFunctorFactors` comparison. The theorem
`residueDualComplexSingleIso_homology` states that its induced homology
map is exactly that original comparison after the native single/homology
identification.

After the chosen A-linear line identification, `nonempty_derivedResidueIso`
gives `D_J(single_A(0,k_A)) ≅ single_A(2,k_A)`. The original signed source
shift from `Shift.lean`, together with the native single/shift comparisons,
then gives `nonempty_derivedResidueDegreeOneIso`:

`D_J(single_A(1,k_A)) ≅ single_A(1,k_A)`.

Here `single_A(1,k_A)` is k_A[-1]. The sign of the native source shift is
retained; it is not replaced by an unsigned reindexing.

## Coefficients and scope

The general derived endpoints display K-injectivity of the actual
coinduced J as a hypothesis. For a supplied `InjectiveResolution R`,
`coinducedResolution_isKInjective` proves it: scalar restriction preserves
monomorphisms, its right adjoint coinduction preserves injectives, and the
actual resolution and its coinduced image are bounded below.
`nonempty_derivedResidueDegreeOneIso_of_injectiveResolution` uses this
proved instance and the actual native resolution inclusion. It has no
coinduced K-injectivity or duality premise.

The finite-length Ext supplier is used with its native same-universe
module inputs and Ext size. Independent derived-model universes are
retained. This does not assert Ext-size invariance for larger module
carriers. No normality or dimension assumption on A, flatness of A over R,
completeness, canonical module, or geometric trace identification is used.
The Postnikov nonzero-arrow consumer and the geometric GR argument have
separate hypotheses and owners.
