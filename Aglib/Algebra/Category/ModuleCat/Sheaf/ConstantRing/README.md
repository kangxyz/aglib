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
