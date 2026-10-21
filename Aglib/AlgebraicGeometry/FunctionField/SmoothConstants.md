# Packet 1 source correspondence

Native source: `Aglib/AlgebraicGeometry/FunctionField/SmoothConstants.lean`.

Frozen source: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.Smooth.Constants`, R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.

SHA-256: `aad28c7eb7f40f601eddbb5335bc184e1aa5c80bcda32eeebdf49e7ce30ccb8b`. Selected lines: `[[16, 65]]`.

The same actual p : X → Spec K defines every chart constant map. Chart smoothness uses Smooth p and an affine open. The generic map additionally uses IsIntegral X. genericConstantMap transparently aliases Scheme.functionFieldConstants; its chart equality includes the literal appLE-to-appTop identity.

| Original declaration | Native declaration | Source line |
| --- | --- | --- |
| `R5Lab.KTheory.MilnorK2.FiniteWitness.SmoothModels.chartConstantMap` | `AlgebraicGeometry.Scheme.chartConstantMap` | 16 |
| `R5Lab.KTheory.MilnorK2.FiniteWitness.SmoothModels.chartConstantMap_smooth` | `AlgebraicGeometry.Scheme.chartConstantMap_smooth` | 22 |
| `R5Lab.KTheory.MilnorK2.FiniteWitness.SmoothModels.nonempty_top` | `AlgebraicGeometry.Scheme.nonemptyTop` | 33 |
| `R5Lab.KTheory.MilnorK2.FiniteWitness.SmoothModels.genericConstantMap` | `AlgebraicGeometry.Scheme.genericConstantMap` | 37 |
| `R5Lab.KTheory.MilnorK2.FiniteWitness.SmoothModels.chartConstantMap_restrict` | `AlgebraicGeometry.Scheme.chartConstantMap_restrict` | 42 |
| `R5Lab.KTheory.MilnorK2.FiniteWitness.SmoothModels.chart_genericConstantMap` | `AlgebraicGeometry.Scheme.chart_genericConstantMap` | 54 |

Compilation evidence and actual provider identities are returned in the assigned scratch manifest. Compilation does not provide a theorem-family witness or mathematical-adoption status.
