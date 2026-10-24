# The actual finite normal cover of a normalized ideal blowup

Companion to `Finite.lean`. This module continues the literal nonzero-ideal
blowup construction in `../NormalizedBlowupCover.lean`; it constructs the
second normalization in the original extension field and its original
B-structure. It does not construct the later map to an arbitrary proper model.

## Inputs and actual objects

The namespace is
`AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover`.
Let `A` and `B` be domains, `J : Ideal A` nonzero, and
`s : Spec B ⟶ Spec A` the original finite dominant structural morphism. The
helpers `specMap_isDominant_of_injective` and `specMap_isFinite` supply these
properties for the literal `Spec.map σ` of an injective finite ring map `σ`.

The finite normal construction assumes `IsNoetherianRing A`,
`ringKrullDim A ≤ 2`, `IsNagataRing.{u, 0} A`, finiteness of the original
`Scheme.functionFieldMap s`, and separability for its exact
`Scheme.functionFieldMapAlgebra s` action. These hold under the assigned
normal Noetherian Nagata local-domain inputs of dimension two and their actual
finite separable fraction-field map. Locality and normality of the original
bases are not needed for this particular construction. The unit ideal is allowed.

The parent `Base.normalization A J hJ` is `X`, the actual generic normalization
of the actual ordinary J-blowup `X₀`. Its original arrow to `Spec A` is `Base.a`.
`FiniteBase.Y A B J hJ s` is the literal relative normalization of
`Spec L ⟶ Spec K(X) ⟶ X`, where `L` is the actual function field of `Spec B`.
`Cover.genericCover_eq_specMap` records the literal scalar map: the inverse of
the original field map of `a`, followed by the original field map of `s`.
`Cover.genericMap_a` proves the original generic square by naturality.
The source of this cover remains the original `Spec L`.

`FiniteBase.pi`, `FiniteBase.b`, and `FiniteBase.eta` are the original map
`Y ⟶ X`, constructed B-structure `Y ⟶ Spec B`, and generic arrow `Spec L ⟶ Y`.
The integral and dominant instances concern these literal objects and maps.

## Normality, finiteness, and the original square

`Cover.genericCover_isFinite` and `Cover.genericCover_etale` use the original
finite separable field map before changing its base along the original field
isomorphism. The native `Scheme.FiniteEtale.GenericNormalization` results then
apply to this very cover. `FiniteBase.pi_isFinite`, `FiniteBase.Y_normalStalks`,
and `FiniteBase.Y_isLocallyNoetherian` derive all their source conditions from
the parent construction and the stated input hypotheses. Normality,
local Noetherianity, finite normalization, and a desired diagram are not added
as premises to this specialization.

The original generic square gives `Spec L ⟶ X ×_A Spec B`. The first projection
is finite. Relative normalization's integral-factor universal map therefore
gives `Y ⟶ X ×_A Spec B`, and its second projection defines `b`.
`FiniteBase.square` is the literal equation

```
pi A B J hJ s ≫ Base.a A J hJ = b A B J hJ s ≫ s.
```

`FiniteBase.eta_b` identifies `eta ≫ b` with the original generic inclusion of
`Spec B`. `FiniteBase.eta_isDominant` is an instance inherited from the actual
`toNormalization` arrow. Cancellation of its injective field map proves
`FiniteBase.b_fieldMap_isIso` on the original field map of `b`.
`FiniteBase.b_isProper` follows from the literal square, proper `a`, finite
`pi`, and separated `s`.

## The same original ideal after nonflat pullback

`FiniteBase.imageIdeal` is the inverse image of `Base.imageIdeal` under `pi`.
`imageIdeal_eq` identifies it with the image of the original affine J-centre
along `pi ≫ a`. `imageIdeal_eq_over_B` identifies the same ideal as
`((affineCenter A J).comap s).comap b`; the B-structure remains the original one.

`imageIdeal_isLocallyRankOne` proves invertibility.
`imageIdeal_nonzero_localFrame` supplies, near every point of Y, an affine open
and a nonzero regular section generating the literal section kernel ideal.
Both use the parent's original ideal-pullback isomorphism and generic avoidance.
Neither normalization map is assumed flat.

The original-coordinate row, section frames, generic coordinate equality,
projective gluing and factorization through the Chow source are assembled
in [FiniteDomination](../FiniteDomination.md). This cover construction
assumes no finite flatness, projectivity of normalization, regular source,
completeness, resolution, or pre-supplied finite diagram.
