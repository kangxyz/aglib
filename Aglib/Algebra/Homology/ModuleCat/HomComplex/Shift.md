# The original signed source shift

`moduleComplexLeftShiftIso R K J s` is an isomorphism

`moduleComplex R K J [-s] ≅ moduleComplex R (K[s]) J`.

It uses the pinned `Cochain.leftShiftLinearEquiv` in every degree. In degree
n, that operation has the original coefficient
`(s*n + s*(s-1)/2).negOnePow`; `moduleComplexLeftShiftIso_hom_f_apply`
identifies the component with that same operation. Its chain-map equation
is exactly `Cochain.δ_leftShift`, together with
`Int.negOnePow_neg`. Thus the shifted differential and its sign agree.

For a K-injective coefficient J, `derivedDualShiftObjIso J K s` gives

`D_J((Q K)[s]) ≅ D_J(Q K)[-s]`.

The composite contains the original Q/shift comparison, both
`derivedDualFactors` comparisons, and Q applied to the inverse of the
chain isomorphism. This is a displayed object comparison, with no global
`CommShift` instance. `HomComplex/Residue.lean` uses s=-1 to place the
residue dual in degree one.

The construction is linear over any ring acting linearly on the source
preadditive category. The derived specialization uses a commutative
coefficient ring and the supplied derived category.
