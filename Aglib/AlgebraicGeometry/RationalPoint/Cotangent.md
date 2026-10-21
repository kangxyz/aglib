# Actual rational-point cotangent pullback

`Cotangent.lean` constructs the cotangent space of the original rational point
as `IsLocalRing.CotangentSpace (pointData x).localRing`. The underlying ring is
the structure-sheaf stalk at `x.left (IsLocalRing.closedPoint k)`. Its base-field
action comes from the same structure morphism, through the existing
`RationalPoint.constants` map. No tangent-space model or scalar-action family is
supplied.

`Scheme.stalkConstantsMorphism` is the categorical structural scalar map: the
inverse field-stalk comparison followed by the structure morphism's original
stalk map. Its naturality lemmas retain this same composite.

`Scheme.stalkMapAt` is the original `Scheme.Hom.stalkMap`, preceded by the native
`stalkCongr` identifying the target point. `Cotangent.localMap` specializes it
to an actual rational-point-preserving morphism, and `Cotangent.map` applies
`Ideal.mapCotangent` to its maximal ideals. The file proves preservation of the
original structural constants, identity and composition formulas, independence
from equality proofs, and zero cotangent pullback for the actual constant map.

For a locally finite type field scheme this same cotangent quotient is finite
dimensional over the original field. Under `SmoothOfRelativeDimension n`, its
dimension is `n`. The proof starts with the existing dimension theorem over the
actual residue field and uses the original section's residue-field equivalence
and structural constants to pass to the base field.

The product calculation uses actual maps. For points `x` and `y`, the two axes
through `lift x y` are

```text
lift (𝟙 X) (toUnit X ≫ y),   lift (toUnit Y ≫ x) (𝟙 Y).
```

Their cotangent restrictions form `axes x y`; the sum of cotangent pullbacks
along the original product projections is `projections x y`. The four scheme
composition identities give identity diagonal terms and zero cross terms, so
`axes_projections` proves `axes ∘ projections = id`. For smooth relative
dimensions `n` and `m`, the original fiber product is smooth of dimension
`n + m`. Thus both cotangent spaces have the same finite dimension and
`axes_injective` follows from the proved surjectivity. No unproved product-stalk
or product-cotangent comparison is assumed.

The current consumer is [MultiplicationCotangent](../Group/MultiplicationCotangent.lean). This is new derived
mathematics, using native Mathlib and the existing
[smooth rational-point constructions](SmoothCurve.lean). All fields and schemes retain
universe `u`; properness, connectedness, characteristic zero and a group law are
unnecessary for the interfaces in this file.
