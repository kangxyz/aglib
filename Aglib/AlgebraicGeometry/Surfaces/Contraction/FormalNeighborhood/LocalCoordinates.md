# The original local source and selected exceptional coordinates

[LocalCoordinates.lean](LocalCoordinates.lean), in
`AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood`, defines
the actual local-spectrum pullback and transports the original exceptional
ideal and selected coordinates to it. These constructions precede the
structure-map bijection and the regularity or dimension conclusions.

For a closed field point `c : Spec k ⟶ Z`, put `z = imagePoint c` and
`R = pointLocalRing c = Z.presheaf.stalk z`. The original closed-point
stalk map is `pointResidueHom c : R →+* k`. It is surjective, and
`ker_pointResidueHom` identifies its kernel with `pointMaximalIdeal c`.
The field `k` is the full original residue field, and no coefficient-field
embedding into `R` is chosen.

For `f : X ⟶ Z`, the construction is

```lean
localSource f z = pullback f (Z.fromSpecStalk z)
localSourceMap f z = pullback.snd f (Z.fromSpecStalk z)
localStructureHom f z : Z.presheaf.stalk z →+* Γ(localSource f z, ⊤)
```

The last map is the literal structural coefficient map of the second
projection. Properness of `f` and local Noetherianity of `Z` give its
finiteness; these properties do not assume its bijectivity.

Let `i : C ⟶ X` be a closed immersion, with `a : C ⟶ Spec k` and
`w : a ≫ c = i ≫ f`. The original pullback lift is
`localExceptional c f i a w : C ⟶ localSource f z`.
The kernel equality `hker : c.ker.comap f = i.ker` makes its residue-fibre
square a pullback and makes this lift a closed immersion. The full original
maximal ideal pulls back to its kernel by
`localExceptional_pointIdeal_comap`.
The flat local-spectrum base change gives `localExceptionalIdealIso` for
the actual ideal modules. It transports local rank one and the original
conormal comparison through `localExceptional_locallyRankOne` and
`localExceptionalConormalIso`.

For the projective application, `C = P¹_k`, the ideal module is
`I_E = Hom.idealModule i`, and `hI` is its local rank-one witness.
The line bundle `H` has specified comparisons
`eI : i^* I_E ≅ O(1)` and `eH : i^* H ≅ O(d)` for `d : ℕ`,
together with the original projective comparison for `H`.
For `1 ≤ n`, let `F` be the original `CartierProjectivePresentation`
with its finite family `F.sections`.
Fix `hn2 : 2 ≤ n * d`, the selected unit-residue position `j₀` with
witness `h₀`, and surjectivity `hρ` of the original residue section map.
The latter makes `c = F.residueToImage eI eH j₀ h₀` a closed immersion.
The first-order data consist of sections `t a` of
`(cartierPowerTwist i hI H n (n * d - 2 + 1)).val` and positions
`q : ULift (Fin 2) → F.index`, with the original equations

```lean
ht : ∀ a, t a ≫ (cartierStepSequence i hI
  (cartierPowerTwist i hI H n (n * d - 2))).g =
    firstOrderQuotientCoordinate i hI H d eI eH n hn2 a
hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)
```

The germ `selectedLocalCoordinate` is taken from the original
`F.pointChartCoordinate` in the same selected chart. Its zero-residue
counterpart `selectedLocalIdealCoordinate` is the original pulled section
transported by `localExceptionalIdealIso`. With the actual fibre ideal
equality, properness of `F.toImage` and local Noetherianity of `F.image`,
`selectedLocalIdealCoordinates_epi` proves that the two selected sections
generate the actual local exceptional ideal; fibre generation and
finiteness are derived in its proof.

The conormal isomorphism `selectedLocalConormalIso` comes from the original
Cartier multiplier and first-order restriction isomorphism.
The theorem `selectedLocalIdealCoordinate_firstOrder` identifies each
selected section, after pullback and this comparison, with its original
`exceptionalCoordinate`. The two sections form `exceptionalCoordinateBasis`
over the full field `k`. These are the coordinates used by
[the structure-map and maximal-ideal theorems](StructureMap.md), without
an independently supplied conormal-generation witness or a replacement
parameter ideal.
