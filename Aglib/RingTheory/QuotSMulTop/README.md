# Scalar-quotient module interfaces

These leaves use Mathlib's actual `QuotSMulTop a M`, the quotient by the scalar
multiple of the whole module, and the native quotient-ring action.

[LocalizedFree](LocalizedFree.lean) proves that the actual quotient module is
free at a prime whenever the original module is free at its contracted prime.
The comparison is the canonical tensor/localization comparison; no finite,
Noetherian or regularity assumption is needed. The punctured-spectrum corollary
uses local-ring instances for the original and quotient rings. It does not
silently infer quotient regularity. The focused
`AglibTest.QuotSMulTopLocalizedFree` consumer checks the original carriers.

[Pi](Pi.lean) compares scalar quotients of finite coordinate products with the
coordinatewise quotient, preserving the original quotient maps.
[Hom](Hom.lean) packages the actual quotient Hom universal property; its exact
annihilation and quotient-action hypotheses remain explicit in the source.
These interfaces feed the quotient-bidual induction in the purity proof.
