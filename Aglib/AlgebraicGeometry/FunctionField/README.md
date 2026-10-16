# Function fields and generic maps

[Basic](Basic.lean) uses the canonical `X.fromSpecStalk (genericPoint X)` and Mathlib function field. For an integral scheme it proves the actual image point, nonempty-open preimages, quasi-compactness and the specified section/germ comparison. No normality, Noetherianity or dimension bound is used.

[Normalization](Normalization.lean) proves that the generic inclusion of an integral scheme with integrally closed stalks has the original scheme as normalization. It then extends an actual generic-fibre map uniquely from a smooth scheme into an integral scheme over that base. The source is not restricted to finite etale schemes. [Finite-etale generic restriction](../Morphisms/FiniteEtale/GenericFiber.lean) consumes this general extension.

These source migrations retain their recorded R5 inputs and canonical maps. Native Lean validation remains a separate phase.
