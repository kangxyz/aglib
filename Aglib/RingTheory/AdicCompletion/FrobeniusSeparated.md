# Separatedness from a bounded Frobenius exponent

Let `R` and `S` be commutative rings with their given `Algebra R S`, and
let `I` be an ideal of `R`. Fix `p e : ℕ` and `ExpChar S p`, so that
`q = p ^ e` is positive. Assume that `algebraMap R S` is injective,
that `S` is reduced, that `R` is `I`-adically Hausdorff, and that
every `s : S` admits `r : R` with `algebraMap R S r = s ^ q`.
Then `IsHausdorff.of_frobenius_pow_mem_range` proves `IsHausdorff I S`
for the original `R`-module action supplied by this algebra structure.

The positive-characteristic case uses `[Fact p.Prime]` and `[CharP S p]`,
which provide `ExpChar S p`. The stated exponential-characteristic interface
also permits `p = 1`. The proof needs no separate characteristic assumption
on `R`, no Noetherianity of either ring, no completeness, and no module
finiteness.

The auxiliary theorem
`Ideal.exists_mem_pow_algebraMap_eq_pow_of_mem_smul_top` proves that
`s ∈ (I ^ n) • (⊤ : Submodule R S)` implies
`s ^ q = algebraMap R S r` for some `r ∈ I ^ (n * q)`.
Its `Submodule.smul_induction_on` argument is induction on finite sums
of products `algebraMap R S a * b`, with `a ∈ I ^ n` and `b : S`.
For each summand, choose `c : R` with `algebraMap R S c = b ^ q`;
then its `q`-th power is the image of `a ^ q * c`, which belongs to
`I ^ (n * q)`. Additivity of `iterateFrobenius S p e` handles the sum.
Membership in `I ^ n S` is never replaced by a single product.

If `s` lies in every `I ^ n S`, choose once a coefficient preimage
`r` of `s ^ q`. For each `n`, the auxiliary produces another preimage
in `I ^ (n * q)`. Injectivity identifies it with the fixed `r`.
Since `n ≤ n * q`, this places `r` in every `I ^ n`; separatedness
of `R` gives `r = 0`. Thus `s ^ q = 0`, and reducedness of `S`
gives `s = 0`.

For normalization applications, the uniform power-image hypothesis must
be proved separately from the field exponent and normality of the actual
base ring. This auxiliary does not assert finiteness or Noetherianity of
that normalization and does not prove the downstream complete local
normalization theorem. It supplies separatedness for the existing
`Module.finite_of_isPrecomplete_of_isHausdorff` consumer.

This is new source over Aglib base
`c6f64b5b133624fae3ad8650f456194180be7ba2`, using Lean `4.34.1` and
Mathlib pin `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Its mathematical suppliers are
`Mathlib/Algebra/CharP/Frobenius.lean`,
`Mathlib/Algebra/Algebra/Operations.lean`,
`Mathlib/RingTheory/Ideal/Operations.lean`, and
`Mathlib/RingTheory/AdicCompletion/Basic.lean`.
