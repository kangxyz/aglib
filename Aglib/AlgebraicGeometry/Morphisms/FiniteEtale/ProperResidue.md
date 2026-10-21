# Uniqueness on a proper model's actual closed fibre

[ProperResidue.lean](ProperResidue.lean) proves faithfulness of the literal
functor

```lean
Scheme.FiniteEtale.baseChange
  (pullback.fst π (Scheme.LocalRing.residueSpecMap R))
```

for `π : Y ⟶ Spec R`, assuming only `CommRing R`, `IsLocalRing R`, and
`UniversallyClosed π`. The instance is
`Scheme.FiniteEtale.ProperResidue.closedFiber_baseChange_faithful`.
`closedFiber_baseChange_reflectsIsomorphisms` also detects isomorphisms of
the original covers: faithfulness reflects mono and epi, and the actual
finite étale category is balanced.
Every proper model satisfies the required universal closedness. The theorem
does not require Henselianity, Noetherianity, flatness or smoothness.

## Relative uniqueness and original projections

The more general theorem `Scheme.Hom.eq_of_closedFiber_pullback_eq`
compares two `Y`-morphisms `f, g : X ⟶ Z`. It assumes that the composite
`X ⟶ Y ⟶ Spec R` is universally closed and that `Z ⟶ Y` is formally
unramified and locally of finite type. There is no unramifiedness assumption
on `Y ⟶ Spec R` or on `Z ⟶ Spec R`.

The relative diagonal gives an open equalizer of `f` and `g` in `X`. Equality
after the actual closed-fibre pullback places that fibre inside the equalizer.
The complement has closed image in `Spec R`. If it were nonempty, its image
would contain the unique closed point, since every point of a local spectrum
specializes there. This would contradict equality on the closed fibre.
Consequently the equalizer is all of `X`.

`LocalRing.ResidueFiber.mem_range_cover_projection_iff` uses the original
two-step pullback and proves

```text
x ∈ range(pullback.fst p (pullback.fst π res))
  ↔ (p ≫ π)(x) ∈ range(res).
```

`cover_projection_residue_square` records the composite of its two original
commuting squares. The forward-cover structural map remains `pullback.snd`,
and `ProperResidue.baseChange_map_fst` records the original first-projection
naturality equation. No replacement residue embedding or isomorphic substitute
functor is introduced.

## Fullness and the remaining existence problem

The separate [Fullness](ProperResidue/Fullness.lean) theorem proves fullness
for actual proper flat models over a Henselian DVR. Together with the
faithfulness above, it makes the literal closed-fibre functor fully faithful
in that scope. Its [mathematical guide](ProperResidue/Fullness.md) records the
more general principal-maximal-ideal hypotheses and the original projection
equations.

The construction lifts the clopen graph of a residue morphism inside the
actual product cover. Finite proper cohomology in degrees zero and one,
stabilization of uniformizer torsion, and Henselian lifting of idempotents
produce that clopen lift. The reflection of isomorphisms proved here makes
its first projection an isomorphism and recovers the prescribed arrow.

Essential surjectivity, which requires lifting an arbitrary finite étale
cover of the closed fibre, remains separate. These results do not supply the
proper-model equivalence over an arbitrary Henselian local ring. The accepted
base-spectrum equivalence in
[HenselianEquivalence](HenselianEquivalence.lean) remains a separate result.
