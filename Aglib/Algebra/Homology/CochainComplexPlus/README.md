# Bounded-below cochain functors and single objects

[Single](Single.lean), imported as `Aglib.Algebra.Homology.CochainComplexPlus.Single`, constructs `CochainComplex.singleFunctorPlus` using the actual single cochain complex and its bounded-below membership. [Functoriality](Functoriality.lean) transports natural isomorphisms and the actual additive-functor composition comparison to `CochainComplex.Plus`.

[NatTrans](NatTrans.lean) gives `CategoryTheory.NatTrans.mapCochainComplexPlus`, its literal component formula, identity/composition laws and the componentwise isomorphism result. The additive/category and zero-morphism hypotheses used to preserve the original lower bound remain explicit; no model of a complex is chosen by the comparison.

These three leaves feed [bounded-below derived functors](../DerivedCategory/README.md), actual Godement total augmentation and scheme direct-image/pullback comparisons. Plus is the bounded-below full category; it does not impose an upper term bound.
