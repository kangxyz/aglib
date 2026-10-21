# Stable freeness after flat base change

`exists_free_prod_of_projective_extendScalars` applies to a finite native
`ModuleCat R` module `M` over a Noetherian local commutative ring `R`, an
actual flat ring homomorphism `f : R →+* S`, and a bound
`HasProjectiveDimensionLE M n`. Its remaining premise is projectivity of
the same scalar extension `(ModuleCat.extendScalars f).obj M`.

The result supplies a finite free native `S`-module `P` such that the
product of that scalar extension with `P` is free. The rings and modules
in this theorem lie in one arbitrary universe. No regularity assumption
or uniform bound on `n` is imposed.

Induction on `n` starts with a finite projective module over a local ring,
which is free. For the next step, take a finite free presentation of `M`.
Its kernel is finite by Noetherianity and has the smaller projective
dimension bound. Flatness preserves the short exact sequence. Projectivity
of the scalar extension of `M` splits that sequence, makes the localized
kernel projective, and yields its actual product equivalence with the
middle term. The inductive complement then gives the desired free product.

The implementation retains the actual homomorphism, short complex,
splitting and product equivalence throughout. It is consumed by
[`PrincipalLocalization.lean`](../../../RingTheory/RegularLocalRing/PrincipalLocalization.lean).
