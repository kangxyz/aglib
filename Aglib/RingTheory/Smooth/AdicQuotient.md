# Formal smoothness of actual adic quotients

Let f:R→S be a flat map of commutative rings and I an ideal of R.
`RingHom.FormallySmooth.quotientMap_pow_of_flat` proves that formal
smoothness of the actual map R/I→S/IS implies formal smoothness of the
actual maps R/Iⁿ→S/IⁿS for every n>0. The statement uses the literal map

```text
Ideal.quotientMap ((I ^ n).map f) f Ideal.le_comap_map.
```

There is no Noetherian, finite-type, finite-generation, or residue-field
perfectness assumption. Flatness is required of the original map f.

`RingHom.Flat.quotientMap` first proves flatness of each actual quotient
map using `Algebra.TensorProduct.quotIdealMapEquivQuotTensor` and native
preservation of flatness under base change. The formal-smoothness proof
then inducts from n to n+1 using the original quotient transition maps.
Their kernels are the images of Iⁿ and IⁿS. The base kernel squares to
zero because I²ⁿ⊆Iⁿ⁺¹ when n≥1. The target kernel is exactly the extension
of the base kernel, by the coefficient equation for the literal quotient
map. These data satisfy Mathlib's existing
`RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero`.

The load-bearing square-zero theorem is
[Stacks Project, Tag 031L](https://stacks.math.columbia.edu/tag/031L),
implemented in `Mathlib/RingTheory/Smooth/Quotient.lean`. That native
proof assumes flatness of the original algebra. Flatness of R/I is not
used.

The current consumer is mixed-characteristic Cohen lifting. For a Cohen
DVR C with uniformizer p, torsion freeness over the integers gives
flatness over the integers. The actual residue marking and unrestricted
perfect-base-field smoothness identify the n=1 map with a formally smooth
prime-field map. This theorem then supplies formal smoothness of every
Z/(pⁿ)→C/(pⁿ), with the actual quotient coefficient maps. The construction
of an arbitrary-residue Cohen DVR and the compatible maps from its
quotients into a given complete local ring remain separate obligations.

Source basis: Aglib HEAD `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Lean 4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
