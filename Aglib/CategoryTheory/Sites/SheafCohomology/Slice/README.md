# Cohomology on an actual site slice

| Source | Interface |
| --- | --- |
| [Adjunction](Adjunction.lean) and [Coproduct](Coproduct.lean) | The actual slice restriction and exact left adjoint built from hom-indexed coproducts and sheafification. |
| [FreeRepresentable](FreeRepresentable.lean) and [ExtComparison](ExtComparison.lean) | The free-representable Ext comparison with literal slice `Sheaf.H`. |
| [Comparison](Comparison.lean), [Naturality](Naturality.lean), [Restriction](Restriction.lean) | Original coefficient, restriction, composition and degree-zero normalization maps. |
| [Ordinary](Ordinary.lean) | The corresponding comparison with Mathlib's original `Sheaf.H'`. |
| [Etale slice comparison](../../../../AlgebraicGeometry/EtaleCohomology/Cohomology/SliceComparison.lean) | Actual small-etale slice entry at scheme universe `u`, coefficient values `u+1` and Ext universe `u+2`, owned by the geometric family. |

The construction keeps the original site and coefficient maps; no derived-etale
adjunction or geometric proper-base-change premise is used. The concrete etale
module-coefficient consumers are documented in
[ModuleCoefficients](../ModuleCoefficients/README.md).
