# Residue layers in a local normalization

Let R be a complete Noetherian normal local domain, let p be a prime, and
write `A = Localization.AtPrime p`. Assume A is a DVR and `R/p` has Krull
dimension at most one. Fix a fraction field K for R and A, a finite purely
inseparable field extension E/K, and the compatible original coefficient
maps into E. Put

```text
S = integralClosure R E,
T = integralClosure A E,
C = R/p,
ℓ = IsLocalRing.ResidueField T.
```

The main result `finite_range_toAtPrimeQuotient_algebraMap` proves that, for
every nonzero x in R, the image of the actual map `S → T/xT` is a finite
R-module. Its more general supplier `finite_range_toAtPrimeQuotient` permits
any nonzero element of T as the quotient generator. These statements do
not assume that S is Noetherian or that T is finite over A. They assert
finiteness of the image, without asserting finiteness over R of the ambient
local quotient.

`toAtPrimeNormalization` is the inclusion S → T whose value in E is the
original element. `toAtPrimeQuotient` composes this inclusion with the
literal principal-ideal quotient map. No replacement of either
normalization or quotient by an unrelated isomorphic ring occurs.

For a global element z of S, `atPrimeOrder p E z j` is the inverse image
of the actual ideal `(z^j)` of T. For nonzero z its membership is equivalent
to `b/z^j ∈ T`. The linear map `atPrimeOrderDivide` uses that actual
fraction in E. `exists_global_uniformizer` starts with a uniformizer of T,
uses localization of integrality to multiply it by a coefficient outside
p, and obtains a uniformizer lying in S. This construction uses no
module-finiteness assertion for T over A.

The denominator theorem works more generally with any positive integer q
such that every q-th power in E belongs to the image of K. Normality gives
`z^q = a` in the image of R. For order j it forms exactly the contracted
ideal

```text
J = comap(R → A)(map(R → A)(span {a^j})).
```

The existing `Ideal.exists_mul_mem_of_map_le_atPrime` supplies one c outside
p with `cJ ⊆ (a^j)`. If b has order at least j, then `b^q` belongs to J.
For a suitable d in R one has `c b^q = a^j d`, whence

```text
(c b/z^j)^q = c^(q-1) d.
```

Thus the particular scaled fraction is integral over R. The denominator
depends on the order j, not on b. Normality of the prime localization is
derived by the native localization theorem for an integrally closed
domain.

`atPrimeResidueQuotientAlgebra` factors the original coefficient map
`R → A → T → ℓ` through the actual quotient C. Its coefficient equation is
`atPrimeResidueQuotientAlgebra_mk`. `exists_residueLayerMap` constructs

```text
H_j → integralClosure C ℓ,
b ↦ residue_T(c b/z^j),
```

and proves that its kernel is the next order layer, viewed as a submodule
of H_j. The target membership follows by mapping the monic equation of the
scaled fraction to the residue field. The kernel equality uses that c is a
unit in T and that z generates its maximal ideal. Consequently the
successive quotient injects into this literal curve normalization.

The final finiteness theorems derive the DVR structure of T and its finite
residue extension from `PurelyInseparable.lean`. The native field
`p.ResidueField`, which is definitionally the residue field of A, is a
fraction field of C. Its actual map to ℓ is compatible with the quotient
algebra just constructed. Completeness of C follows from finite-module
completeness and the image formula for maximal ideals. `CompleteCurve`
then proves `integralClosure C ℓ` finite over C and hence over R. This
retains arbitrary inseparability in the residue extension.

`finite_atPrimeOrder_layer` obtains finite generation of the successive
quotients. `finite_quotient_atPrimeOrder` uses their finite short exact
filtration. Factoring a nonzero element of the DVR T as a unit times a
power of z identifies the filtration quotient with the image in the
specified local principal quotient.

The surface consumer must supply the DVR property of its actual
height-one localization, the dimension bound on its actual prime quotient,
and the compatible fraction-field towers. The global product injection
and the final finiteness of a two-dimensional normalization are outside
this leaf.

Source basis: Aglib HEAD `c6f64b5b133624fae3ad8650f456194180be7ba2`,
Lean 4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The source implements the residue-layer argument in the supplied fixed
normalization-2d-v1 mathematical proof. Its dependencies are the imported
Lean suppliers; no excellence, Japanese-ring, coefficient-field, or Cohen
structure theorem is imported as a premise.
