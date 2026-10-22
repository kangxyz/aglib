# Minimal integral models of original pointed genus-one curves

Let `R` be a DVR, with `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
Let the original field `K` carry the actual fraction-field structures
`[Algebra R K] [IsFractionRing R K]`. All coefficient and base maps use this
`algebraMap R K`.

The inputs are the original `X : FScheme K`, `Curve.Properties X`, a section
`p : Spec K ⟶ X.left` with `p ≫ X.hom = 𝟙 _`, and
`coherentGenus K X = 1`. Thus `X` is smooth of relative dimension one, proper
and geometrically connected. There is no characteristic, perfectness or group
hypothesis, and a Weierstrass presentation or pointed comparison is not an input.

`exists_minimal_pointed_equation` constructs an actual equation
`V : WeierstrassCurve R`. Its discriminant is nonzero, and its coefficient
extension satisfies the unchanged native predicate

```lean
WeierstrassCurve.IsMinimal R (V.map (algebraMap R K))
```

This is Mathlib's valuation comparison among integral equations obtained by
native admissible variable changes. It retains the native integrality guard
and the original multiplicative discriminant valuation. The theorem returns
an actual isomorphism over the original `Spec K` from `X` to the literal cubic
of the mapped equation, carrying `p` to its actual infinity section. The ring
and field universes are independent in this statement.

`exists_minimal_pointed_genericFibre` returns the categorical version when `R`
and `K` lie in the same universe, as required by the existing native coefficient
base-change interface. Its target is literally

```lean
Over.mk (pullback.snd (structureMap V)
  (Spec.map (CommRingCat.ofHom (algebraMap R K))))
```

The original section maps to `baseChangedInfinitySection (S := K) V`, the
literal categorical pullback of the integral infinity section. The isomorphism
is the proved original pointed presentation, followed by the inverse of the
native minimum variable-change comparison, followed by the existing canonical
coefficient-base-change isomorphism. No field is replaced and no identification
of schemes in different universes is asserted.

Both theorems also return integrality of the actual total scheme and properness
and flatness of its actual `structureMap V`, using the existing projective cubic
and its two monic charts over the original domain. The integral
discriminant can be a nonunit. Consequently these results do not assert
smoothness or regularity of the total model, a resolution, or a minimum among
all regular models.
