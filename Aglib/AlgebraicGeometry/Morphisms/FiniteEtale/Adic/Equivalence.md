# Finite etale equivalence over a complete Noetherian local base

[Equivalence.lean](Equivalence.lean) proves the actual residue base-change
equivalence under the explicit assumptions

```lean
(R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
[IsAdicComplete (IsLocalRing.maximalIdeal R) R]
```

All interfaces are in `AlgebraicGeometry.Scheme.FiniteEtale.Adic`.

## Literal residue functor

`residue_baseChange_isEquivalence` proves

```lean
(Scheme.FiniteEtale.baseChange
  (Scheme.LocalRing.residueSpecMap R)).IsEquivalence
```

`residueEquivalence R` is an actual categorical equivalence from finite etale
covers of `Spec R` to finite etale covers of `Spec (IsLocalRing.ResidueField R)`.
Its forward functor is definitionally the displayed native base-change
functor, as recorded by `residueEquivalence_functor`. The object structural
map is the literal `pullback.snd`; `residueEquivalence_functor_obj_hom` states
this equality. The theorem `residueEquivalence_functor_map_fst` retains the
original first-projection equation for the native pullback of each morphism.

Fullness is exactly `quotient_baseChange_full R (maximalIdeal R)` from
[Fullness.lean](Fullness.lean). The quotient's algebra map is definitionally
the actual residue map. Faithfulness and essential surjectivity are the
existing instances from [ResidueLift.lean](../ResidueLift.lean), whose proofs
need only locality. `Functor.asEquivalence` packages these proved properties;
no coordinate-algebra lifting argument is duplicated.

## Marked residue field

For `F : Type u` with `[Field F]` and an actual ring equivalence
`e : IsLocalRing.ResidueField R ≃+* F`, `marked_closed_isEquivalence R e`
proves equivalence of the exact functor

```lean
Scheme.FiniteEtale.baseChange
  (Spec.map (CommRingCat.ofHom
    (e.toRingHom.comp (IsLocalRing.residue R))))
```

`markedClosedEquivalence R e` is the corresponding categorical equivalence.
Its forward functor is definitionally this expression, as recorded by
`markedClosedEquivalence_functor`. A marking in the reverse direction is
passed by taking its inverse.

The proof reuses `marked_closed_full R e` from [Residue.lean](Residue.lean).
Faithfulness and essential surjectivity transfer through the actual scheme
isomorphism `Spec.map e` and the native `baseChangeComp` and `baseChangeId`
isomorphisms. The ring-map composite remains `e ∘ residue R`.

The current completed-rational-point consumer uses
`Scheme.RationalPoint.Completion.Ring q` and
`Scheme.RationalPoint.Completion.residueEquiv q`. Substituting these into
`marked_closed_isEquivalence` gives the same literal functor already present
in [RationalPointCompletion.lean](RationalPointCompletion.lean). That existing
file and its scalar structures were left unchanged.

## Scope

These interfaces retain their complete Noetherian hypotheses and marked-residue
maps. The more general [Henselian residue equivalence](../HenselianEquivalence.md)
proves equivalence over any Henselian local base without completeness or
Noetherianity. Neither base-spectrum result asserts the closed-fibre comparison
for every proper scheme over the base.
