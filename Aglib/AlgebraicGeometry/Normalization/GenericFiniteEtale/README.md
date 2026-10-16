# Normalization of generic finite etale schemes

[Basic](Basic.lean) uses Mathlib relative normalization of the composite from the given finite etale scheme over `X.functionField` to `X`. The actual integral-closure charts recover the same generic scheme as the literal pullback. Its only base premise is integrality; no normality, local Noetherianity, dimension bound, or nonempty generic cover is assumed.

[Finite](Finite.lean) adds locally Noetherian base and integrally closed actual stalks to prove that the canonical structural morphism is finite. [Stalks](Stalks.lean) derives local Noetherianity and integrally closed domain stalks from the actual finite field factors and chart open immersions. [Dimension](Dimension.lean) proves equality with the base stalk dimension at the actual structural image under those same stated base premises. Split and empty covers remain allowed; these leaves do not supply global etaleness or integrality/nonemptiness of the total normalization.

The lower inputs have their broader mathematical owners: [affine normality](../../Properties/Normal/Affine.lean), [integral going-down stalk dimensions](../../Stalk/IntegralExtension.lean), [function-field maps](../../FunctionField/README.md), and [finite-etale integral closure](../../../RingTheory/IntegralClosure/FiniteEtale.lean). Generic restriction full faithfulness is in [Morphisms/FiniteEtale/GenericFiber](../../Morphisms/FiniteEtale/GenericFiber.lean).

Each source leaf records the frozen R5 source identity. Source correspondence and wrapper-body substitution do not claim native elaboration or independent proof acceptance.
