# Maps between finite cyclic coefficient levels

`CoefficientMaps` reuses `ZMod.castHom` for reduction and constructs
`ZMod.divisorInsertion` by multiplication of integer representatives by `n / d`
for `d ∣ n`. Injectivity retains the nonzero target-level hypothesis. The two
composite formulas are multiplication by the quotient, and the mixed product
formula retains the literal reduction map.

Consumers include cyclic-character factorization and the supplied unit-character
actions in `Aglib.Algebra.Group.Action.CyclicCoefficients`. Neither a cyclotomic
character nor a geometric coefficient marking is constructed here.
