# Module Ext

[FiniteLength](FiniteLength.lean) proves that the original Ext-one module into a Noetherian local ring has finite length when the finite source module is projective (in particular free) at every nonmaximal localization. The proof uses the original connecting map, finite-presentation denominator clearing and the native closed-point support criterion; it does not replace Ext by an unrelated model or require regularity or projective dimension at most one.

Other leaves in this developing family retain their own source contracts and validation records. This guide does not assert completion of the Auslander or purity theorem.

[FinitePi](FinitePi.lean) gives the actual linear finite-product comparison for
Ext, including the native module-length formula used in the Auslander bound.
[DualQuotient](DualQuotient.lean) identifies the original dual reduction modulo
a scalar with Hom into the quotient ring. The scalar is regular on the ring
and the original first Ext into the ring vanishes. Its Noetherian local
finite-module endpoints prove scalar-Ext Nakayama and dual-freeness lifting,
without any projective-dimension-at-most-one hypothesis.

[QuotSMulTop](QuotSMulTop.lean) proves actual degree-one change of rings for a
regular scalar on the quotient of a short exact presentation with free middle
term. No projective-dimension-one assumption is imposed on the final module;
the first syzygy need not be free. The focused consumer keeps the Ext universe
independent of the ring/module carrier universe.

[Localization](Localization.md) treats every nonnegative Ext degree over a
Noetherian commutative ring, with finite source and arbitrary coefficients.
`ModuleCat.extPostcomp_isLocalized_of_finite` proves that postcomposition
with the original coefficient-localization map localizes Ext.
`ModuleCat.extScalarExtension_isLocalized_of_finite` proves the corresponding
property for the original extension-of-scalars `mapExtLinearMap`.

The comparison keeps the actual extension/restriction adjunction unit and
its pointwise equation, together with original source-endomorphism
precomposition. It uses finite free covers and Noetherian syzygies, without
local-ring, finite-projective-dimension or regular-sequence premises. The
carrier and Ext universes are the ones declared by the native scalar
adjunction interfaces.

[ScalarRegularity](ScalarRegularity.md) proves regularity of a scalar on native
`Ext M N q`, for any natural degree, from its regularity on `M` and vanishing
of Ext from the original `QuotSMulTop` quotient. The commutative ring and
modules need no finiteness or projectivity. The canonical-stalk consumer must
supply that quotient vanishing from its geometry.
