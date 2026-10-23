# Finite purely inseparable normalization over a complete normal local surface

Let `R` be a complete Noetherian normal local domain of Krull dimension at
most two, `K` its given fraction field, and `E/K` any finite purely
inseparable field extension. All coefficient actions are the original
`Algebra R K`, `Algebra K E`, and `Algebra R E`, with `IsScalarTower R K E`.
The theorem
`integralClosure.finite_of_complete_local_normal_dimLE_two_of_isPurelyInseparable`
proves `Module.Finite R (integralClosure R E)` for the literal integral
closure inside `E`. It assumes neither Noetherianity nor completeness nor
module finiteness of that integral closure.

The intermediate theorem
`integralClosure.finite_scalar_quotient_of_complete_local_normal_dimLE_two`
proves finiteness of `QuotSMulTop x (integralClosure R E)` for every nonzero
`x : R`. Let `S = integralClosure R E`. The finite index set consists of
the actual minimal primes of `Ideal.span {x}`. Each has height one, so its
actual localization `R_p` is a DVR. Since `x` is nonzero and belongs to
`p`, the dimension inequality for the actual surjection `R → R/p` gives
`dim(R/p) + 1 ≤ dim R ≤ 2`, hence `dim(R/p) ≤ 1`.
This dimension estimate only needs an ideal containing the nonzero x;
primeness is used by the subsequent localization and normalization arguments.

For each index, put `T_p = integralClosure R_p E`, with the unique
localization action extending the original coefficient map to `E`. The
source proves compatibility with `R_p → K → E` by uniqueness of the
localization lift.
`integralClosure.finite_range_toAtPrimeQuotient_algebraMap` supplies finiteness of the
actual image `U_p = range(S → T_p / x T_p)`. The proof uses
`LinearMap.pi` on these maps restricted to their ranges. It does not
assert that the ambient modules `T_p / x T_p` are finite over `R`.

The kernel is exactly `x • (⊤ : Submodule R S)`. To prove the nontrivial
inclusion, choose a common positive exponent `q` from the finite purely
inseparable extension and write `b ^ q = r` through the actual map from
`R`. Local vanishing implies `b/x ∈ T_p` at each minimal prime over
`x`. These are all height-one primes containing `x`. Normality of `R_p`
therefore makes `(b/x)^q` an actual coefficient in `R_p`, so `r` is
locally divisible by `x^q`. At the remaining height-one primes, `x` is
a unit and the same local divisibility holds. The existing height-one
principal-ideal membership theorem for the normal base `R` gives
`x^q ∣ r` in `R`. Consequently `(b/x)^q` lies in the actual image of
`R`, which proves integrality of `b/x` and hence `b ∈ xS`.

The quotient-kernel equivalence embeds `S/xS` into the finite product of
the `U_p`. The source applies Mathlib's `Submodule.CoFG.ker`, which uses
that existing equivalence; Noetherianity of `R` makes the image finite.
The actual product has a single named carrier and module structure shared
by its map and its Noetherianity theorem. A generic quotient-finiteness
lemma keeps the kernel conversion independent of this concrete product.
If the maximal ideal of `R` is nonzero, choose a nonzero `x` in it and apply
`integralClosure.finite_of_isPrecomplete_of_finite_scalar_quotient`.
That supplier proves separatedness for the original `R`-module action
using finite sums and Frobenius. If the maximal ideal is zero, the
complete-curve theorem handles the field case.

This implements steps 6 and 7 of the independently reviewed normal-base
argument in
`tmp/inputs/aglib-surface-review-20261023/normalization-2d-v1/normal_surface_proof.md`.
The residue-layer finiteness and coefficient-lifting arguments remain in
their existing owners. Reduction of arbitrary finite extensions to this
purely inseparable theorem, and verification of hypotheses for proposed
geometric consumers, are separate obligations.

Source basis: Aglib `c6f64b5b133624fae3ad8650f456194180be7ba2`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean `4.34.1`.
