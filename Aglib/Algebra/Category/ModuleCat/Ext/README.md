# Degree-one module Ext

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
