# Bounded-below cochain functors and single objects

[Single](Single.lean), imported as `Aglib.Algebra.Homology.CochainComplexPlus.Single`, constructs `CochainComplex.singleFunctorPlus` using the actual single cochain complex and its bounded-below membership. [Functoriality](Functoriality.lean) transports natural isomorphisms and the actual additive-functor composition comparison to `CochainComplex.Plus`.

[NatTrans](NatTrans.lean) gives `CategoryTheory.NatTrans.mapCochainComplexPlus`, its literal component formula, identity/composition laws and the componentwise isomorphism result. The additive/category and zero-morphism hypotheses used to preserve the original lower bound remain explicit; no model of a complex is chosen by the comparison.

These three leaves feed [bounded-below derived functors](../DerivedCategory/README.md), actual Godement total augmentation and scheme direct-image/pullback comparisons. Plus is the bounded-below full category; it does not impose an upper term bound.

[Shift](Shift.lean) proves that the original componentwise natural
transformation and original composition comparison commute with native
integer shifts. The proof transports through the fully faithful inclusion
and its actual shift comparisons; it respects mathlib's deliberately
irreducible induced shift structures. No identity formula for those induced
shift arrows or alternative shift structure is imposed. The category and
morphism universes are independent, and only preadditivity/additivity is
needed. Original derived composition units and base-change descents consume
these same comparison maps.

[QuasiIsoShift](QuasiIsoShift.lean) proves shift stability of the original
bounded-below quasi-isomorphism property. Its proof uses the inclusion's
actual shift comparison and the original unbounded quasi-isomorphism
property's arrow-isomorphism invariance. This supplies the native
localization hypothesis for right-derived descent, without changing shifts.
