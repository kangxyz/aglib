# The original projective image point is regular of dimension two

[Projective.lean](Projective.lean) proves
`CartierProjectivePresentation.pointLocalRing_regularLocal_dimension_two` in
`AlgebraicGeometry.Scheme.Surfaces.Contraction`. Its target is the original
`pointLocalRing (F.residueToImage eI eH j₀ h₀)`, which is exactly the stalk of
the original schematic image at the original full residue-field point.

The data are an actual closed projective embedding over a commutative
Noetherian ring, its specified finite coordinate labeling, the original
Cartier embedding `i : P¹_k ⟶ X` over any field `k`, its ideal module's
local rank-one witness `hI`, and the original
`CartierProjectivePresentation F` for `1 ≤ n`. The specified comparisons are
`eI : i^* (Hom.idealModule i) ≅ O(1)` and `eH : i^* H ≅ O(d)`
for a line bundle `H` and `d : ℕ`; the original projective comparison for
`H` is retained. The selected position `j₀` has unit original
residue coefficient, with witness `h₀`.
The premise `hρ` is surjectivity on global sections of the original
`cartierResidueMap`. The two original first-order lifts `t` satisfy the
literal Cartier quotient equations `ht`, and `q : ULift (Fin 2) → F.index`
records their positions through
`hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)`.
The numerical condition is `hn2 : 2 ≤ n * d`; the precise lift types and
quotient equations are recorded in
[LocalCoordinates](../FormalNeighborhood/LocalCoordinates.md).

The actual image inclusion gives local Noetherianity. The actual presentation
triangle gives properness of `F.toImage`, and the original residue-map
surjectivity makes `F.residueToImage` a closed immersion. The published
point-ideal theorem identifies the original fibre ideal with the original
exceptional Cartier ideal.

Write `c = F.residueToImage eI eH j₀ h₀`, `z = imagePoint c`,
`R = pointLocalRing c` and `W = localSource F.toImage z`.
The two selected germs at `q ⟨0⟩` and `q ⟨1⟩` generate the actual maximal
ideal of `R` by
`FormalNeighborhood.selectedLocalStructureAndParameters`. This same theorem
proves bijectivity of the literal original map
`localStructureHom F.toImage z : R →+* Γ(W, ⊤)`. Native P1 is
regular by its actual smooth structure map over `k` and is connected through
its proved integrality. The actual local-source theorem in
[Regularity](../Regularity.md) therefore gives a normal domain structure on
the same target stalk through that proved structural-map bijection.

The original first-order degree-one basis proves that its maximal ideal is
nonprincipal via `selectedLocalMaximalIdeal_not_isPrincipal`. The ring theorem
`IsLocalRing.regularLocal_dimension_two_of_span_pair` now proves both
`ringKrullDim = 2` and `IsRegularLocalRing` for that same stalk. A global-section
isomorphism, normality, or a dimension bound is not an additional input.
The field `k` remains the full original residue field throughout; no section
of its residue homomorphism is chosen.

This is the local regularity result at the actual image point. The
[point-blowup criterion](../PointBlowup.lean) has its own hypotheses and
retains the original universal Cartier-ideal lift. Applying it to recognize
the original global morphism as the inverse blowup, assembling global
contraction and factorization, and the resolution applications remain upper
obligations.
