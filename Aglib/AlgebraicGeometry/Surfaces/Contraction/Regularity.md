# Regularity of the original local source

[Regularity.lean](Regularity.lean) concerns the actual local-spectrum pullback
defined in [LocalCoordinates](FormalNeighborhood/LocalCoordinates.lean).
Its data are a closed field point `c : Spec k ⟶ Z`, a proper map `f : X ⟶ Z`,
a closed immersion `i : C ⟶ X`, and `a : C ⟶ Spec k` with
`w : a ≫ c = i ≫ f`. The actual kernel equality
`hker : c.ker.comap f = i.ker` identifies the original closed fibre.

Write `z = imagePoint c`, `W = localSource f z`,
`b = localSourceMap f z`, and `j = localExceptional c f i a w`.
The structural coefficient map is the literal
`α = localStructureHom f z : pointLocalRing c →+* Γ(W, ⊤)`.
All public declarations lie in
`AlgebraicGeometry.Scheme.Surfaces.Contraction`.

- `localSource_connectedSpace c f i a w hker` assumes `ConnectedSpace C` and
  proves `ConnectedSpace W`. It needs no regularity, Noetherianity or
  global-section-map hypothesis.
- `localSource_regularStalks c f i a w hker hI hC` assumes locally Noetherian
  `Z`, local rank one `hI` of the actual `Hom.idealModule i`, and
  `hC : RegularStalks C`. It proves `RegularStalks W` without any condition
  on the structural coefficient map.
- `localSource_normalStalks` gives `NormalStalks W` on the same data.
- `localSource_isIntegral` additionally assumes `ConnectedSpace C` and proves
  `IsIntegral W`.
- `pointLocalRing_isDomain_and_isIntegrallyClosed_of_localStructureHom_bijective`
  additionally takes the explicit premise
  `Function.Bijective (localStructureHom f z)` and proves that the original
  `pointLocalRing c = Z.presheaf.stalk z` is a normal domain.

The original residue map is surjective. Its spectral map therefore is a closed
immersion, and its closed point maps to the closed point of the original local
spectrum. The existing actual fibre pullback square and its canonical inverse
pullback isomorphism lift every point over this closed point to `C`.
The [Cartier regular-quotient theorem](../../IdealSheaf/Cartier/RegularQuotient.lean)
gives regularity at its image. The
[closed-point propagation theorem](../../Properties/Regular/ClosedPoints.lean)
then gives regularity everywhere on the proper local source. Regular-local
normality gives its normal domain stalks.

For connectedness, every closed point of `W` lies in `j(C)`. Every nonempty
closed subset of the compact T0 space `W` contains a closed point. Pulling a
clopen set back to connected `C` gives the empty set or the whole space; applying
the closed-point observation to that set or its complement proves that the
original clopen set is empty or the whole space. The connected normal-component
theorem then gives integrality of `W`.

The [global-sections theorem](../../Properties/Normal/GlobalSections.lean) gives
normality of the actual global section ring of `W`. Only at the last step is
the supplied bijectivity of the original `localStructureHom` used to transfer
this normal-domain conclusion to the original target stalk. The generic
theorem retains that premise explicitly. For the original projective Cartier
presentation, [the formal-coordinate construction](FormalNeighborhood/StructureMap.md)
supplies it by `selectedLocalStructureAndParameters`.

No ambient normality or regularity, excellence, coefficient field, separability,
or dimension hypothesis is assumed. The conclusion of this generic module is
the normal-domain transfer with its displayed premise.
[The projective application](Regularity/Projective.md) combines that transfer
with the proved original structure-map bijection and first-order maximal-ideal
parameters to prove regularity and dimension two of the actual image stalk.
Global inverse-blowup recognition and contraction remain further obligations.
