# Length of scalar torsion

For any commutative ring `R` and any `R`-module `M`,
`Submodule.length_torsionBy_mul_le b d` proves

```text
length_R M[b*d] ≤ length_R M[d] + length_R M[b].
```

Here `M[a]` is the original `Submodule.torsionBy R M a`, and every length is
Mathlib's `Module.length` in `ℕ∞`. The ring and module can inhabit independent
universes. No Noetherianity, domain, locality or finite-generation assumption
is imposed.

The proof uses the actual linear map `M[b*d] → M[b]`, `x ↦ d • x`. The
inclusion of `M[d]` identifies it with this map's kernel. Exact length
additivity is applied with target the map's actual range, and the inclusion
of that range into `M[b]` gives the inequality. Surjectivity onto all of
`M[b]` is unnecessary.

`Submodule.length_torsionBy_pow_le c r` gives
`length_R M[c^r] ≤ r * length_R M[c]`, including `r = 0` since `M[1] = 0`.
`Submodule.length_torsionBy_le_of_dvd_pow a c r h` uses the actual torsion
inclusion associated to `h : a ∣ c^r` and concludes
`length_R M[a] ≤ r * length_R M[c]` with the same module and scalar action.

The current B1 consumer is the uniform fixed-scalar bound for original
`H¹(X, O_X)` on normal proper birational surface models. Once a nonzero
reduced principal equation `c` with `a ∣ c^r` and a uniform finite bound on
the original `c`-torsion have been constructed, this file supplies the final
power and divisibility step. The reduced-principal construction and the
actual total-divisor comparison through its proper transform remain separate,
unimplemented B0–B1 obligations. This file proves the intermediate algebraic
inequalities and does not assert the full geometric uniform bound.
