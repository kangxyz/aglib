# Constant-ring coefficient constructions

The original ringed and module-valued realizations are supplied by
[Basic](Basic.lean), [Pullback](Pullback.lean) and [Underlying](Underlying.lean).
These leaves reuse their actual ring maps, coefficient equivalence and units.

| Source | Interface |
| --- | --- |
| [UnitDetection](UnitDetection.lean) | Transport of the original inverse-image unit under a functor, using the actual equivalence and adjunction. |
| [Exactness](Exactness.lean) | Actual local-surjection, finite-limit and homology transfer; injectives are preserved through the genuine module adjunction. |
| [ScalarRestriction](ScalarRestriction.lean) | The original scalar ring map, sectionwise restriction and coefficient/sheafification comparisons. |
| [Torsion](Torsion.lean) | Internal local-annihilator torsion and the sufficient positive scalar-unit annihilator criterion. |
| [Torsion/Derived](Torsion/Derived.lean) | The same torsion condition on original homology objects in the supplied derived model, including its Plus subcategory. |

Site, ring, module-value and derived universes retain their stated ranges.
No finiteness assumption on the underlying coefficient group is introduced.

[UnderlyingComposition](UnderlyingComposition.lean) derives the underlying
values of the original direct-image composition from its site-isomorphism
section maps. The original adjunction mates reflect that equation to
inverse-image composition; literal equality transport feeds the existing
whole source-cube construction. It uses the same ringed images and
coefficient equivalences, with arbitrary ring and independent site worlds.

[PointFibre](PointFibre.lean) applies the existing constant-ring coefficient equivalence and the supplied point's module fibre. Its whole underlying additive comparison uses the same point-sized filtered colimits and coefficient comparison, keeping site, Hom, scalar, module-value and point worlds separate.
