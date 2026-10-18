# Milnor K-theory

The canonical group is `MilnorK.K F n`, for a field `F` and any `n : ℕ`.
It is the actual free integer module on ordered unit tuples, quotiented by
coordinatewise multiplicativity and adjacent Steinberg relations. Its symbol
laws and universal property are proved from that quotient.

```lean
import Aglib.KTheory.MilnorK

open MilnorK

example (F : Type*) [Field F] : K F 0 ≃ₗ[ℤ] ℤ := zeroEquiv F
```

Import focused leaves when fewer dependencies are needed:

| Import below `Aglib.KTheory.MilnorK` | Interface |
| --- | --- |
| `Basic` | `K`, `symbol`, `IsSymbolMap`, quotient descent `lift` and extensionality |
| `Map` | Actual field-hom maps, identity and composition across independent universes |
| `LowDegree` | Degree zero is ℤ; degree one is the additive group of units |
| `Product` | Bilinear concatenation, honest degree transport, units and associativity |
| `Symbols`, `TupleSymbols` | Sign identities and adjacent symbol manipulations |
| `CompatibilityK2`, `CompatibilityK3` | Symbol-preserving inverse comparisons with the tensor presentations |
| [Residue](Residue/README.md) | Specialization, tame residues and actual DVR realization |
| [Norm](Norm/README.md) | Polynomial and finite-extension norms |
| [Dedekind](Dedekind/README.md) | Finite-support residues, pushforward and algebraic reciprocity |

The small `Aglib.KTheory.MilnorK` facade exports the basic group, field maps,
low degrees, product and low-degree residue compatibility. `Norms` is the
optional finite-extension tower entry; production implementations use leaves.

All declarations live under `MilnorK`. The specialized tensor models are
`MilnorK.K2.Group F` and `MilnorK.K3.Group F`; their symbols and valuation data
live in those same subnamespaces. They are proof and comparison interfaces,
not independent top-level theories. General clients use `K F n`; `twoEquiv`
and `threeEquiv` identify the ordered symbols in both presentations.

The basic group, product, sign and residue constructions work in arbitrary
characteristic. Norms on arbitrary finite field extensions currently require
characteristic zero and the displayed algebra/finite-dimensional/tower data.
Specialization retains a chosen uniformizer. Tame residue independence is
proved separately under the documented normalization and compatibility inputs.
Characteristic two retains the diagonal `-1` formula, not unsupported alternation.

The library depends only on Mathlib and lower Aglib owners. Field, DVR,
completion, norm and local-length helpers live in their own algebraic subjects.
Motivic consumes these objects for diagonal and weight-two comparisons. Its
`AffineEndpointGeometry` and `NormalizedAffineEndpointNorm` applications stay
downstream with the original geometric cycle objects.

[Source correspondence](../../../docs/migration/motivic-milnor-k.json) records
the admitted modules and reused native interfaces.
Original identifiers in retained source comments refer to that source snapshot;
the declarations and import table above give the current API. This relocation
changes ownership and names, not mathematical hypotheses.
