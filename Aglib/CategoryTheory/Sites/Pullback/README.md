# Actual coefficient pullback constructions

| Source | Interface |
| --- | --- |
| [FlatCoefficients](FlatCoefficients.lean) | Preservation and reflection of the actual flat abelian left Kan extension, and the original four-factor coefficient comparison with its unit law. |
| [RepresentedTarget](RepresentedTarget.lean) | The chosen Kan/pullback comparison to the supplied actual target, with full unit, adjunct and naturality laws. |
| [DenseRestriction](DenseRestriction.lean) | Faithfulness of actual continuous restriction from cover density. |
| [FiniteProducts](FiniteProducts.lean) | The original product comparison and finite-power value construction using the selected endpoint products. |

The coefficient functor, target, universal property and comparison factors are
the actual supplied ones. The pure APIs keep independent site and value worlds;
geometric existence and cover hypotheses are supplied by native consumers.
