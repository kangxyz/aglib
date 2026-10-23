# The original structure map and maximal-ideal parameters

[StructureMap.lean](StructureMap.lean) proves the local structure-map
bijection for the actual schematic image of a Cartier projective
presentation. Its declarations lie in
`AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood`.
The local source, residue map and selected coordinates are those of
[LocalCoordinates](LocalCoordinates.md).

Take a closed embedding `p : X ⟶ ProjectiveSpace A ι` over a commutative
Noetherian ring `A`, a finite coordinate labeling `eι : ι ≃ Fin (r + 1)`,
and the original Cartier embedding `i : P¹_k ⟶ X` over a field `k`.
Write `I_E = Hom.idealModule i`, with local rank-one witness `hI`.
For a line bundle `H`, the specified comparisons are
`eI : i^* I_E ≅ O(1)`, `eH : i^* H ≅ O(d)` and `H ≅ p^* O(1)`,
where `d : ℕ`.
For `1 ≤ n`, let `F` be the original `CartierProjectivePresentation`;
its finite family is `F.sections`.

The theorem `selectedLocalStructureAndParameters` uses the following
specified data of this same family:

- `hn2 : 2 ≤ n * d` and a position `j₀ : F.index` whose original residue
  coefficient is a unit, with witness `h₀`;
- `hρ`, surjectivity on global sections of the original `cartierResidueMap`;
- two sections `t a` of
  `(cartierPowerTwist i hI H n (n * d - 2 + 1)).val`, indexed by
  `a : ULift (Fin 2)`, whose original Cartier quotient images are
  `firstOrderQuotientCoordinate i hI H d eI eH n hn2 a`, as specified by `ht`;
- positions `q : ULift (Fin 2) → F.index` with the literal equations
  `hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)`.

Write `c = F.residueToImage eI eH j₀ h₀`, `z = imagePoint c`,
`R = pointLocalRing c`, `W = localSource F.toImage z` and
`α = localStructureHom F.toImage z : R →+* Γ(W, ⊤)`.
For each of the two indices, write
`u a = selectedLocalCoordinate i hI H d F eI eH j₀ h₀ (q a)`.
The theorem proves both

```lean
Function.Bijective (localStructureHom F.toImage z)
pointMaximalIdeal c = Ideal.span {u ⟨0⟩, u ⟨1⟩}
```

Thus the ideal equality concerns the actual maximal ideal of the original
image stalk and the actual selected germs. The full residue-field map is
`pointResidueHom c : R →+* k`; its kernel is this maximal ideal. No section
of that map, target normality, or assumed global-section isomorphism enters
the construction.

The selected local ideal sections generate the original local exceptional
ideal. Proper formal functions gives vanishing of the dual Cartier first
cohomology; the original two-section Koszul row and finite Nakayama then
give surjectivity of `α`. Injectivity comes from the original schematic-image
stalk map through the ordinary local-sections comparison. With that
bijection, the same Koszul row identifies the original base ideal with the
displayed span.

The separate theorem `selectedLocalMaximalIdeal_not_isPrincipal` proves
`¬ (pointMaximalIdeal c).IsPrincipal` from the same first-order equations.
It assumes quasi-compactness and quasi-separatedness of `F.toImage` and
closedness of `c`; it does not require the structure-map bijection or any
normality, regularity or dimension conclusion. The canonical
`selectedLocalConormalMap` is semilinear for the full `pointResidueHom c`
and sends the two selected germs to the original basis of `Γ(P¹_k, O(1))`.
This basis correspondence excludes a principal maximal ideal.

For any quasi-compact, quasi-separated `f : X ⟶ Z`,
`ordinaryUnit_localStructureHom` identifies the stalk map induced by the
original `f.c` with `localStructureHom f z` through
`ordinaryStalkLocalSectionsEquiv f z`.
The theorem `ordinaryUnit_stalk_isIso_of_localStructureHom_bijective`
therefore gives its stalk isomorphism from bijectivity of that literal map.
For the original projective image, `selectedLocalStructureAndParameters`
supplies this premise at `z`.

[Projective regularity](../Regularity/Projective.md) uses these conclusions
to prove that the same image stalk is regular of dimension two. Recognition
of the original global morphism as the inverse blowup and a global
contraction theorem remain upper obligations.
