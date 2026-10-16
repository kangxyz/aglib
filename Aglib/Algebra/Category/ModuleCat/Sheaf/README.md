# Module sheaves on arbitrary sites

The objects are actual module sheaves over a ring sheaf on a site, before scheme specialization. Tensor statements retain commutative coefficient rings where required. [Tensor/Basic](Tensor/README.md) owns the single sheafified tensor bifunctor and unit/braiding maps.

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

[Epimorphisms](Epimorphisms.lean) proves that forgetting scalars preserves the displayed shaped colimits and epimorphisms, and that an epi of module sheaves is locally surjective. The site, sheafification, local-bijectivity and sheaf-composition hypotheses remain explicit; this does not assert surjectivity of sections over every object.

[Presentation](Presentation.lean) owns `SheafOfModules.generatingSections_ofEpi_isIso`, `finitePresentation_map_isFinite` and the basis-preserving presentation transport helpers. The supplied unit isomorphism, colimit preservation and original generator/relation index types are retained. [Quasicoherent pushforward](Quasicoherent/README.md) transports these actual finite presentations along compatible site functors. [Local bases](LocallyFree/README.md) supplies the corresponding local-basis pushforward and arbitrary-site locality before scheme specializations.
