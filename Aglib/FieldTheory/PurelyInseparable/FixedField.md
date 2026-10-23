# The full automorphism fixed field of a normal extension

Import `Aglib.FieldTheory.PurelyInseparable.FixedField`.

For fields `K` and `M` with the given `K`-algebra structure and
`[Normal K M]`,
`IntermediateField.isPurelyInseparable_fixedField_top K M` proves

```lean
IsPurelyInseparable K
  (IntermediateField.fixedField (⊤ : Subgroup (M ≃ₐ[K] M)))
```

The fixed field is the actual intermediate field of the original extension.
Its maps to and from the base and ambient fields are the existing canonical
inclusions. No separability or characteristic assumption is imposed, and
finite-dimensionality is unnecessary.

The proof uses the characterization of pure inseparability by uniqueness of
embeddings into an algebraic closure. Each embedding of the fixed field over
`K` extends to an embedding of `M`, because normality makes `M` algebraic.
Use one extension as the ambient embedding. Normality turns any other extension
into an automorphism of `M` over `K` relative to this embedding. That automorphism
fixes every element of the full fixed field, so the two original embeddings
coincide.

The current consumer is the finite-normal-hull reduction for normalization of
a complete Noetherian normal local domain of dimension two. If `M/K` is finite
and normal, its full automorphism fixed field `F` is finite and purely
inseparable over `K`; the existing finite-group fixed-field theorem makes
`M/F` Galois. This module supplies the pure-inseparability statement. It does
not assert that an arbitrary normal extension `M/K` is separable or finite.
