# The native Koszul differential modulo the square of the maximal ideal

`LinearPart.lean` uses the original tensor Koszul complex and its original
two-column inclusions and projections. Its main interface is
`ChainComplex.Koszul.mem_maximalIdeal_smul_top_of_d_mem_sq`.

For a commutative local ring `R`, put `m = maximalIdeal R`. Let
`f : Fin e → m` have linearly independent cotangent classes over the residue
field, and put `s = List.ofFn (fun j => (f j : R))`. In every degree `i`, the
theorem gives

```text
d_(i+1,i)(z) ∈ m² • K_i  →  z ∈ m • K_(i+1),
```

where `K = ChainComplex.Koszul.chainComplex s` is the actual tensor complex.
It includes `e = 0` and all degrees beyond the length. No Noetherianity,
regular-sequence hypothesis or residue-characteristic restriction is required.

The degree-one proof constructs coefficients from the original projections.
The actual boundary becomes their linear combination of the entries, so
cotangent independence forces every coefficient into `m`. For higher degrees,
the shifted projection and list induction first put the shifted component into
`m`. Its product with the new entry lies in `m²`; the old projection and the
same induction then put the old component into `m`. The original inclusions
reconstruct the result.

The module also supplies `chainComplex_free_X` through the native two-column
linear equivalence and reexports the existing `chainComplex_finite_X` instance.
This statement is one input to the residue-projective-dimension comparison; it
does not assert the full Serre regularity criterion.
