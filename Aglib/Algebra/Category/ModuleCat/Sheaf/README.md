# Generic site module tensors and comparisons

The objects are actual module sheaves over a commutative-ring sheaf on a site, before scheme specialization. [Tensor/Basic](Tensor/README.md) owns the single sheafified tensor bifunctor and unit/braiding maps.

| Focused leaf | Main interface/result and premises |
| --- | --- |
| [TensorAdditive](TensorAdditive.lean) | Additivity of the actual tensor functors under the stated site/sheafification conditions. |
| [TensorFiniteFree](TensorFiniteFree.lean) | Tensor with a finite free sheaf is the actual finite-coproduct functor, with the original injection formula. |
| [TensorExact](TensorExact.lean) | A supplied retract of a finite free coefficient sheaf preserves actual short exact sequences after tensoring. The finite index and chain-compatible retract data are explicit. |
| [TensorInjectiveRetract](TensorInjectiveRetract.lean) | Tensor with a finite free coefficient, or its supplied retract, preserves an actual injective object. The injective input and finite/retract data remain explicit. |
| [TensorSections](TensorSections.lean) | Actual tensor sections, pure-tensor map formulas and hom-extensionality. |
| [SheafificationPushforward](SheafificationPushforward.lean) | The canonical sheafification/direct-image comparison, with continuity, cocontinuity, weak sheafification and local-bijectivity conditions retained. |
| [TensorPushforward](TensorPushforward.lean) and [TensorPushforwardMap](TensorPushforwardMap.lean) | Actual tensor/direct-image maps and unit/section formulas; their isomorphism comparison requires the original invertible coefficient map and compatible site/sheafification assumptions. |

Imports use `Aglib.Algebra.Category.ModuleCat.Sheaf` followed by the named leaf. General scheme module tensors, finite-locally-free tensor exactness, Godement and projection formula are consumers. Invertible sheaves specialize the generic tensor rather than defining another implementation.
