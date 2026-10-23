# Scalar quotient bounds in dimension at most one

For a Noetherian domain `R` of dimension at most one and a nonzero scalar
`a`, `QuotSMulTop.length_of_finite_torsionFree` proves

```text
length_R(M / a M) = finrank_R(M) * length_R(R / a R)
```

when `M` is finite and torsion-free. The notation `R / a R` here is the
literal module `QuotSMulTop a R`. The ring need not be local or complete.
Choose a finite independent family of full rank and its free span `F`.
Rank-nullity makes `M / F` torsion, so the lower finite-torsion theorem
gives it finite length. Additivity of the existing principal Euler
expression cancels this quotient. The free calculation follows through the
actual quotient-product equivalence. The proof does not assert that `M`
itself is free.

`QuotSMulTop.length_le_of_rank_lt_aleph0` gives the corresponding upper
bound for an arbitrary torsion-free module whose cardinal rank is below
`Cardinal.aleph0`, without finite generation of that module.
`QuotSMulTop.isFiniteLength_of_rank_lt_aleph0` extracts finite length.
The finite-rank hypothesis is distinct from finite generation and is
satisfied by submodules of a finite-dimensional fraction-field vector
space. `QuotSMulTop.isFiniteLength_of_finite` also supplies finite length
of a nonzero scalar quotient for any finite module, including torsion
modules.

`Module.length_le_of_fg_image_bound` says that a surjective linear map
`f : M →ₗ[R] N` has target length at most `b : ℕ∞` if every image `P.map f`
of a finitely generated submodule `P ⊆ M` has length at most `b`. It applies
over any ring and permits the modules to have different universes.

For each finite strict chain of submodules of `N`, choose a witness for
every strict inclusion and lift those witnesses along `f`. Their span is
finitely generated. Restricting the original chain to its image preserves
every strict inclusion, so that image detects the full chain length.
Taking the supremum of chain lengths proves the bound.

`QuotSMulTop.length_le_of_fg_submodule_bound` applies this argument to
the literal scalar quotient `M / a M`, over a commutative ring. The induced
map `P / a P → M / a M` is used through its image. Injectivity of that map
is neither required nor asserted. A natural-number bound yields
`QuotSMulTop.isFiniteLength_of_fg_submodule_bound`.

The numerical theorem supplies the bound hypothesis of this generic
finite-witness passage. The complete-curve consumer uses it both for
the finite residue module and for Noetherianity of the normalization.
Finiteness of a normalization over its base does not appear as an input.

This is new source over Aglib base
`22f7532679eec4295167fcf885cf8b1b0981d899`, using Mathlib pin
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The mathematical finite-witness
step is also the last paragraph of Stacks Project, Lemma 10.119.9,
[Tag 00PE](https://stacks.math.columbia.edu/tag/00PE), inspected on
2026-10-23. The finite-rank calculation here uses the existing scalar
Euler sequence instead of that source's asymptotic sandwich argument.
