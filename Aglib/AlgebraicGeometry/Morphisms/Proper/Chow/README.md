# Proper modifications over finite projective products

[Basic](Basic.lean) supplies the unconditional theorem
`Scheme.Chow.exists_finite_projective_product_modification`. For every actual
proper `f : X → Spec R` over a Noetherian commutative ring, it constructs
finite coordinate types, their native `projectiveProductOver`, a scheme `Y`,
maps `p : Y → X` and `q : Y → projectiveProductOver`, and a dense open `V`.
The original `p` is proper and surjective, the original `q` is finite, and
`p ∣_ V` is invertible. The literal pair `pullback.lift p q comm` is a closed
immersion, with `comm` the displayed original structural equation.
The cover and affine projective immersions are supplied internally.
There is no reducedness, integrality, field, finite-dimensionality or
pre-supplied Chow/finiteness family premise; the empty source is included.

[GraphProduct](GraphProduct.lean) starts with `f : X → S`, finitely many actual
schemes `P i` over `S`, opens `U i` of `X`, and actual compatible maps
`h i : U i → P i`. Every component is the original native graph image from
[GraphClosure](../GraphClosure.lean). Its `modelOver` is the native finite
product of those components over `X`; `targetOver` is the native finite product
of the original `P i` over `S`.

The actual original `toSource` and `toTarget` satisfy the structural equation.
Their literal native pullback pairing `pair` is a closed immersion, proved by
the product of the original `imageι` maps and the canonical finite-product
base-change comparison. `toTarget_π` identifies every target coordinate with
the original corresponding graph-closure projection. If each `P i → S` is
proper, `toSource` is proper; if every `U i` is dense, it is also surjective.
These results do not assume Noetherianity or reducedness. The empty family
retains the actual identity map of `X`.

[GraphProduct.Restriction](GraphProduct/Restriction.lean) assumes precisely
that each `U i → X` is quasi-compact, in addition to properness of the targets.
`isIso_toSource_restrict` proves that the original `toSource ∣_ V` is invertible
for every `V ≤ U i` for all `i`; `toSourceRestrictIso_hom` is its literal map.
In particular, `isIso_toSource_commonOpen` applies to the actual finite
intersection. A locally Noetherian source supplies the quasi-compactness
premises. The proof uses native restriction pullback squares and the same
finite-product base-change comparison, with no alternative graph product.

`toTarget_π_restrict` retains the original local graph equation on the inverse
image of each `U i`. [FiniteProductMap](FiniteProductMap.lean) uses this equation
and the literal closed pairing to prove that the original `toTarget` restricted
to that open is an immersion whenever each original `h i` is an immersion.
These local results retain properness of the targets and quasi-compactness of
each original `U i → X`. If the `U i` cover, `toTarget_locallyQuasiFinite` supplies local quasi-finiteness.
If `f` is proper, `toTarget_isProper` supplies properness and
`toTarget_isFinite` applies native Zariski's Main Theorem. These hypotheses
still require neither reducedness nor Noetherianity.

The producer uses the proved finite dense affine cover and the actual
affine-open projective immersion over the original structural map. Its target
is the displayed finite native product, so a Segre embedding is not needed
for this geometric endpoint. It does not assert scheme-theoretic dominance,
the full separated finite-type Chow theorem, or proper coherent cohomological
finiteness. The
[cohomological Chow consumer](../../../Cohomology/Proper/Chow/README.md)
now applies the proved projective-product suppliers to these original maps:
the same modification, chosen independently of every coefficient, has both
uniform bounded coherent derived images and finite original cohomology.
The [proper-finiteness consumer](../../../Cohomology/Proper/Finiteness/README.md)
now closes the support-cone induction over every Noetherian affine base,
as recorded by the owning [Proper guide](../README.md).

[Projective](Projective.lean) strengthens the target of this same modification.
`Scheme.Chow.exists_projective_modification` constructs a closed immersion
`j : Y ⟶ ProjectiveSpace R (ULift (Fin (m + 1)))` with
`j ≫ toSpec R _ = p ≫ f`. The original scheme `Y`, proper surjective map `p`,
and dense isomorphism open `V` are unchanged. The base is any Noetherian
commutative ring, and `f` is proper, including the empty-source case. The proof
uses the [finite-product Segre embedding](../../../ProjectiveSpace/Segre/FiniteProduct.lean)
and the [finite-map embedding](../../../ProjectiveSpace/FiniteProductEmbedding.lean);
it does not identify a finite map with a closed immersion.
[Proper Grothendieck existence](../../../Cohomology/GrothendieckExistence/Proper.md)
uses the resulting actual projective embedding to realize the formal pullback
on the Chow source.
