# The original ring map of an affine-open factorization

Source: [OpenChartFactor.lean](OpenChartFactor.lean).

For commutative rings `R,T`, an open immersion `a : Spec R → X` and
`c : Spec T → X` with `range c ⊆ range a`,
`affineOpenChartFactor a c hc` is `Spec.preimage` of the native
open-immersion lift. Its Spec map satisfies `Spec.map factor ≫ a = c`
and this equation characterizes the factor uniquely.

If `c` is also an open immersion, so is the Spec map of the factor.
No separation, Noetherianity, flatness or homology condition is imposed.
