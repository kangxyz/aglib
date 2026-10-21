# Packet 1 source correspondence

Native source: `Aglib/AlgebraicGeometry/RationalPoint/FiniteField.lean`.

Frozen source: `R5Lab.Aglib.AlgebraicGeometry.RationalPoints.FiniteField`, R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.

SHA-256: `402ccce9aaa83d53b29b2845b967411ddd072d8e1eba6e25b8680c06f31ba3d4`. Selected lines: `[[35, 112]]`.

All three source statements retain the original Fintype k premise. The general result retains LocallyOfFiniteType X.hom and QuasiCompact X.hom. The set is the actual hom-set from the monoidal unit in FScheme k, selected by a finite affine cover. A declaration-local unusedFintypeInType exception preserves the source premise without a global linter change.

| Original declaration | Native declaration | Source line |
| --- | --- | --- |
| `R5Lab.Galois.FrobeniusBounds.Actual.finite_algebraHom` | `AlgebraicGeometry.Scheme.RationalPoint.finite_algebraHom` | 35 |
| `R5Lab.Galois.FrobeniusBounds.Actual.finite_affineRationalPoints` | `AlgebraicGeometry.Scheme.RationalPoint.finite_affineRationalPoints` | 44 |
| `R5Lab.Galois.FrobeniusBounds.Actual.finite_rationalPoints` | `AlgebraicGeometry.Scheme.RationalPoint.finite_rationalPoints` | 79 |

Compilation evidence and actual provider identities are returned in the assigned scratch manifest. Compilation does not provide a theorem-family witness or mathematical-adoption status.
