# Polynomial Japanese stability

`IsJapaneseRing.polynomial` states that a Noetherian Japanese domain `R` has
a Japanese polynomial ring. It uses `IsJapaneseRing.{u, 0}` on both sides.
No normality, perfection, separability, locality or dimension hypothesis is
imposed on `R`.

For a finite purely inseparable extension of the literal field
`FractionRing R[X]`, the original fractions supply rational presentations
over `FractionRing R`. The
[finite constant-root theorem](../../FieldTheory/PurelyInseparable/FiniteConstantRoots.md)
constructs an actual
finite constant field `E` in the algebraic closure of the supplied extension,
and a root `z` of a positive characteristic power of the original variable.

The model is the literal polynomial ring `(integralClosure R E)[X]`. Its
`R[X]` action evaluates the original variable at `X^(p^e)`. Products of
coefficient generators with the powers `X^i`, for `i < p^e`, explicitly span
this model. Its fraction field is the actual field `E(z)`, and polynomial
normality places every integral element of the original extension in this
finite model. Noetherianity then gives finite normalization. The generic
normal-hull reduction supplies the arbitrary finite-extension case.

The argument corresponds to section P of the Nagata-stability derivation.
[RationalAdjunction](RationalAdjunction.md) and
[FiniteTypeSurface](FiniteTypeSurface.md) use this polynomial Japanese
result with their own original coefficient maps and dimension bounds.
It does not by itself assert the Nagata property for every finite-type
algebra over an arbitrary Japanese domain.
