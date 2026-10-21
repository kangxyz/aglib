# Packet 1 source correspondence

Native source: `Aglib/AlgebraicGeometry/RationalPoint/FieldExtension.lean`.

Frozen source: `R5Lab.Aglib.AlgebraicGeometry.RationalPoints.FieldExtension`, R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.

SHA-256: `ddaa5424e1c95a2c1d966a0a8487e460451712b33f265a42155ccab432bf0901`. Selected lines: `[[23, 104]]`.

The point map uses the native chosen closurePointArrow/closureEmbedding, the literal Over pullback adjunction and scalarExtensionMap i. Only the bijection/equivalence needs IsFinite X.hom. Naturality is for arbitrary schemes. The absolute-Galois compatibility retains CharZero F and CharZero K.

| Original declaration | Native declaration | Source line |
| --- | --- | --- |
| `R5Lab.P16CompletionTorsion.pullbackPointEquiv` | `AlgebraicGeometry.Scheme.RationalPoint.pullbackPointEquiv` | 23 |
| `R5Lab.P16CompletionTorsion.pointExtensionMap` | `AlgebraicGeometry.Scheme.RationalPoint.pointExtensionMap` | 31 |
| `R5Lab.P16CompletionTorsion.pullbackPointEquiv_left` | `AlgebraicGeometry.Scheme.RationalPoint.pullbackPointEquiv_left` | 36 |
| `R5Lab.P16CompletionTorsion.pointExtensionMap_fst` | `AlgebraicGeometry.Scheme.RationalPoint.pointExtensionMap_fst` | 44 |
| `R5Lab.P16CompletionTorsion.pointExtensionMap_bijective` | `AlgebraicGeometry.Scheme.RationalPoint.pointExtensionMap_bijective` | 52 |
| `R5Lab.P16CompletionTorsion.pointExtensionEquiv` | `AlgebraicGeometry.Scheme.RationalPoint.pointExtensionEquiv` | 58 |
| `R5Lab.P16CompletionTorsion.pointExtensionMap_naturality` | `AlgebraicGeometry.Scheme.RationalPoint.pointExtensionMap_naturality` | 65 |
| `R5Lab.P16CompletionTorsion.closurePointArrow_galois` | `AlgebraicGeometry.Scheme.RationalPoint.closurePointArrow_galois` | 77 |
| `R5Lab.P16CompletionTorsion.pointExtensionMap_galois` | `AlgebraicGeometry.Scheme.RationalPoint.pointExtensionMap_galois` | 93 |

Compilation evidence and actual provider identities are returned in the assigned scratch manifest. Compilation does not provide a theorem-family witness or mathematical-adoption status.
