# A degree-p complement for one coefficient

Let `k` be any field of prime characteristic `p`, and let `c : k` lie
outside the literal Frobenius image `(frobenius k p).fieldRange`.
`Subfield.exists_nonPowerComplement` produces an actual subfield `E ⊂ k`
which contains that image, is maximal among such subfields avoiding `c`,
and satisfies `IntermediateField.adjoin E {c} = ⊤`. The field may have
infinite p-rank.

The scalar action is the canonical subfield inclusion `E → k` throughout.
`frobeniusCoefficient` is the original element `c^p`, regarded as an element
of `E`; its coercion theorem is an equality to `c^p` in `k`.
`nonPowerComplementPresentation` constructs

```text
IsAdjoinRootMonic k (X ^ p - C (frobeniusCoefficient p E hE.prop.1 c)).
```

Its map is evaluation at the original `c`, and
`nonPowerComplementPresentation_root` proves that its root is exactly `c`.
`nonPowerComplementBasis` is the resulting `Basis (Fin p) E k`, with
`nonPowerComplementBasis_apply` identifying its `i`-th value as `c^i`.
Finiteness and degree `p` of the ambient extension are derived from this
basis; no ambient `FiniteDimensional E k` premise is used to construct it.
The public theorem `purelyInseparable_of_frobenius_le` supplies the
pure-inseparability witness used in the exposed presentation constructor.

The maximal field is obtained by Zorn's lemma. A nonempty chain of
subfields containing the Frobenius image and avoiding `c` has its union
as an upper bound with those same properties. For every element outside
the maximal field, its purely inseparable element exponent is exactly one,
so its simple adjunction has degree `p`. Maximality puts `c` in that
adjunction. The simple adjunctions of `c` and the element then have equal
finite degrees and one contains the other, so they coincide. This shows
that every element of `k` belongs to `E(c)`.

The current consumer is the single fixed-series entrance to R.B7. If a
series in `k[[u,v]]` has only p-divisible exponents but has a coefficient
`c ∉ k^p`, the returned basis is the coefficient input to the
`MvPowerSeries.FiniteCoefficientExpansion` supplier, using the original
coefficient map followed by `expand p`. The monic presentation is also
the coefficient-field input to the one-root algebraic differential
construction. The two/three-generator series presentation, coefficientwise
derivation, fraction-field differential detection, and the later B5--B7
trace and cohomology arguments remain separate obligations.

This is a single-coefficient construction. It does not assert directedness
or intersection properties for maximal avoiding subfields.
[Stacks 07P2](https://stacks.math.columbia.edu/tag/07P2) supplies a parallel
existence proof by extending the singleton to a p-basis. The present
construction uses Zorn and the actual simple intermediate fields directly.
