# Rank-one cancellation

`StableRankOne.lean` constructs a cyclic generator of an `R`-module `M`
from an actual basis indexed by `Fin (n + 1)` of `M × (Fin n → R)`.
Here `R` is any commutative ring. Neither freeness nor projectivity of `M`
is a premise.

The cofactor alternating map takes `n + 1` vectors in this product to `M`.
On the tuple consisting of `(m, 0)` and the standard coordinate vectors
it has value `m`. Expansion in the supplied basis expresses every such
value as a scalar multiple of its value on that basis. This proves
`Module.exists_smul_eq_of_basis_prod` with an actual generator.

`Ideal.isPrincipal_of_free_prod` applies this construction to a nonzero
ideal `I` in a domain. Its premises are a finite free module `N` and a
finite free product `I × N`. Inclusion of `I` into `R`, and multiplication
by a nonzero member of `I` in the opposite direction, give injections
between `I × Rⁿ` and `R × Rⁿ`. The two rank inequalities identify the
required basis size. The conclusion is native `I.IsPrincipal`.

This is the cancellation step used by
[`PrincipalLocalization.lean`](../../RingTheory/RegularLocalRing/PrincipalLocalization.lean).
It uses native bases, alternating maps and determinants; it introduces no
alternative module or stable-freeness structure.
