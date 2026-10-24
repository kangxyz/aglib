# The first nonzero derived homology layer

For a left-exact additive functor `F` and an actual bounded-below object
`K ≥ 1`, the module supplies the comparison
`H¹(RF(K)) ≅ F(H¹(K))`.

Apply the installed right-derived functor to the native triangle
`τ<2 K → K → τ≥2 K`. Lower t-exactness puts the last image in degrees at
least two, so the original first arrow induces an isomorphism on `H¹`.
The first object is concentrated in degree one. Its native normalized
single comparison, followed by the original `H¹` inclusion, identifies it
with the single of `H¹(K)`.

The comparison for that single uses the original single shift, the
installed derived functor's shift comparison, the native homology shift,
and `rightDerivedSingleHomologyZeroIso`. Only preservation of finite limits
by `F` is used. There is no assertion that `F` is exact, no positive upper
bound on `K`, and no assumption that higher direct images vanish.

The current consumer is the original positive truncation of derived
pushforward in the low-degree Leray construction.
