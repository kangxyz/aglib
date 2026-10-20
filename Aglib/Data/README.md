# Finite indices and coefficient levels

[Fin](Fin/README.md) documents cyclic rotation on `Fin (n + 1)`:
rotation-invariant functions are constant, and the no-fixed-point statements
retain `1 < n`. Its actual consumers include
[FinRotate](../GroupTheory/Perm/FinRotate.lean) and
[CyclicEnumeration](../GroupTheory/Perm/CyclicEnumeration.lean).

[Nat](Nat/README.md) records positive divisible levels and the quotient
arithmetic used by cyclic coefficient maps. [ZMod](ZMod/README.md) owns
`ZMod.castHom` reduction and `ZMod.divisorInsertion`, defined by multiplying
integer representatives by the quotient `n / d` for `d ∣ n`. Injectivity retains
the nonzero target-level hypothesis. The composite formulas are multiplication
by that quotient; the mixed product formula keeps the literal reduction map.

Consumers are [cyclic character factorization](../GroupTheory/Cyclic/CharacterFactorization.lean),
[supplied unit-character actions](../Algebra/Group/Action/CyclicCoefficients.lean)
and [roots-of-unity coordinate levels](../RingTheory/RootsOfUnity/CoordinateLevels.lean).
These lower maps construct neither a cyclotomic character nor a geometric
coefficient marking. Each focused leaf retains its original level hypotheses.
