# Normalization in an arbitrary finite function-field extension

[FiniteFunctionField.lean](FiniteFunctionField.lean) starts with an integral
scheme X and the original field L carrying a specified K(X)-algebra.
It constructs the actual composite

    Spec L → Spec K(X) → X

and uses its literal relative normalization. The original toNormalization
and fromNormalization arrows satisfy their native composition equation;
the normalization is integral and both original arrows are dominant.

For every nonempty original affine open U, chartFunctionFieldMap is the
section map of the original generic cover. chartBaseAlgebra is the literal
section map of the composite to X. chartScalarTower proves their original
factorization through K(X). The equality of the inverse-image open with
the whole Spec L gives chartFieldIso to the same original L, and
chartFunctionFieldMap_fieldIso proves that it preserves the originally
specified field action. No replacement extension field is introduced.
The finite-extension closure proofs use local field structures retaining
the original chart CommRing; they do not replace the public section-ring
algebras or install a competing global field instance.

When L is finite over K(X), the same chart section algebra is finite over
K(X). Its integral closure over Γ(X,U) is normal by the arbitrary-finite
field-extension theorem. The native normalizationObjIso transports this
to the original normalization sections, and localization at the original
chart point proves normalization_normalStalks. Normality of X and
separability of L/K(X) are not hypotheses.

fromNormalization_isFinite assumes explicitly that each original nonempty
affine chart ring Γ(X,U) is Nagata. Its Japanese-domain consequence gives
finiteness of the literal integral closure through the original
Γ(X,U)→K(X)→Γ(Spec L,γ⁻¹U) scalar tower. The original
fromNormalization_app equation then proves finiteness of the actual
relative-normalization map. Empty opens use their zero section rings.
If X is locally Noetherian, the same finite map makes its normalization
locally Noetherian.

This common normalization family has no surface dependency. Producing the
chart Nagata hypothesis by GF2 for a particular normalized surface blowup
is a separate consumer. The source does not infer that hypothesis from
normality or from a finite extension alone, and makes no finite-flat or
finite-etale claim.
