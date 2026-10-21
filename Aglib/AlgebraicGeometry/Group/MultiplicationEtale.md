# Actual multiplication: proved slice and first-order gap

The invertible-level interface is now supplied by
[MultiplicationInvertible](MultiplicationInvertible.lean), over every field.
This leaf retains its general conditional interface; its theorem premises
are unchanged.

`MultiplicationEtale.lean` proves, over any characteristic-zero field, that
`(𝟙 G.X) ^ n` is finite, etale and surjective when `G` is a native
`Grp (FScheme k)`, `Curve.Properties G.X` holds, and `(𝟙 G.X) ^ n ≠ 1`.
`multiplication_finite_etale_of_point` replaces the last condition with an
actual test-scheme point `x : T ⟶ G.X` satisfying `x ^ n ≠ 1`.
The supplied point is a witness, not a manufactured coordinate group.

`pointedGroupLaw_multiplication_finite_etale_of_ne_one` retains the exact
`PointedGroupLaw C c` and its stored `GrpObj C`. Multiplication by one is
unconditionally finite etale and surjective in every characteristic, without
the curve hypotheses.

The proof first uses `MultiplicationFinite.lean` to derive finiteness and
surjectivity from nonconstancy. `Curves.Isogeny.Etale` then supplies etaleness
through actual generic-field separability, a generic etale neighborhood,
translations over an algebraic closure, and faithfully flat descent. No
etaleness, flatness or differential theorem family is a parameter.

The original target is the finite and etale part of
`EllipticMultiplicationGeometry` at
`R5Lab/AlgebraicGeometry/EllipticCurve/Isogenies/CyclotomicDualKernel.lean:283–286`,
in the supplied packet at R5Lab `f8a3314ddecffcada2ec721d26d56a937bed9690`.
That target assumes only `0 < n` and `IsUnit (n : k)`. It remains open: the
nonconstancy hypothesis above has not been discharged from those assumptions.

The precise next native obligation is the first-order power formula at the
actual identity. Let `e = η[G.X].left (IsLocalRing.closedPoint k)`, let
`R = G.X.left.presheaf.stalk e`, and let `m = IsLocalRing.maximalIdeal R`.
The proved pointed equation identifies `((𝟙 G.X) ^ n).left e` with `e`.
Use this equality's native `stalkCongr` and the actual `Scheme.Hom.stalkMap` to
form the local ring endomorphism `φ_n : R →+* R`. The missing statement is

```text
for every a ∈ m,  φ_n(a) - (n : R) * a ∈ m ^ 2.
```

This is the identity `[n]^* = n` on the actual cotangent space `m / m²`.
It must be derived from the native group multiplication and unit maps.
The current differential-sheaf API constructs actual pullback maps and proves
identity/composition formulas, but does not provide the product-cotangent
comparison at the identity needed to prove this power formula.

The subsequent nonconstancy argument has its dimension input already available:
`RationalPoint.localRing_finrank_cotangentSpace` in
`RationalPoint/SmoothCurve.lean` gives dimension one for the actual origin stalk.
An invertible `n` acts nontrivially on this space, while the constant origin map
acts as zero. Proving and connecting the first-order formula would therefore
finish the characteristic-zero finite-etale statement through the present
producer. In positive characteristic one must additionally derive etaleness
from the invertible first-order map; the characteristic-zero separability
theorem does not cover that case. The existing
`LocalRing.Etale.exists_etale_neighborhood_of_stalkMap_formallyEtale` and
`Curve.etale_of_nonempty_etale_open` provide the downstream local-to-global
steps once the actual stalk's formal etaleness is established.

No degree `n * n`, rank-two basis, Weil pairing, Cartier pairing, or Picard/Hilbert
representability conclusion is proved here. The finite carrier of the existing
literal multiplication kernel is an eligible conditional consumer; its
cardinality is not determined by these results.
