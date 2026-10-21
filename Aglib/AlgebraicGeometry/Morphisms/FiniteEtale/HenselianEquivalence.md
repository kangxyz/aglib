# Henselian residue equivalence

[HenselianEquivalence.lean](HenselianEquivalence.lean) proves that the literal
finite étale residue base-change functor

```lean
Scheme.FiniteEtale.baseChange (Scheme.LocalRing.residueSpecMap R)
```

is full and is an equivalence, under `CommRing R` and `HenselianLocalRing R`.
The declarations are in `Scheme.FiniteEtale.HenselianEquivalence`:

- `residue_baseChange_full` supplies `Functor.Full`.
- `residue_baseChange_isEquivalence` combines fullness with the faithfulness
  and essential surjectivity from [ResidueLift](ResidueLift.lean).
- `residueEquivalence` chooses the equivalence with this exact forward functor.

No Noetherian, DVR, completeness, excellence, characteristic or separable
closedness assumption on the residue field is required. The result concerns
the base spectrum. It does not prove `ProperHenselianComparison R` or the
closed-fibre comparison for a proper scheme over `R`.

## The missing morphism-lifting step

Choose an algebraic closure `Ω` of the residue field `k`, with its actual
point `s₀ : Spec Ω ⟶ Spec k`. Write `B` for residue base change, `G` for the
geometric fibre functor over `k`, and `H` for the geometric fibre functor over
`R` at `s₀ ≫ residueSpecMap R`. The native pullback equivalence gives
`e : H ≅ B ⋙ G`.

For two covers `X` and `Y`, the finite set of all functions `H(X) → H(Y)`
has the continuous action

```text
(g · f)(x) = g_Y(f(g_X⁻¹(x))).
```

Continuity follows by factoring through the finite discrete permutation groups
of the two fibres. The proved Galois reconstruction theorem represents this
finite continuous action by an actual finite étale cover `Z` over `R`.

A morphism `B(X) ⟶ B(Y)` gives an element of this function set fixed by the
action from `Aut G`. Its corresponding point of `G(B(Z))` is therefore fixed.
Fullness of the Galois action functor over `k` turns that fixed point into a
section of `B(Z)`. Its composite with the actual first pullback projection is
a residue point of `Z`.

[HenselianResidue.existsUnique_section_lift](HenselianResidue.lean) lifts this
point to a section of the same cover `Z`, preserving both structural and
restriction triangles. The chosen geometric point of `Z` is consequently fixed
by all of `Aut H`. Hence the original function `H(X) → H(Y)` is equivariant.
Fullness of the Galois action functor over `R` produces a morphism `X ⟶ Y`;
faithfulness of `G` shows that its literal residue pullback is the prescribed
morphism.

The Galois-category and fibre-functor instances used here are proved suppliers
from [GaloisInstances](GaloisInstances.lean), not additional theorem premises.
Their finite-cover quotient construction uses the proved finite locally
constant sheaf representation theorem. The local spectrum is connected because
every point specializes to its closed point. The only Henselian input is the
existing residue-section lifting theorem, proved through standard étale
algebras and simple-root Hensel lifting.

## Original maps

`residueEquivalence_functor` identifies the forward functor literally with
residue base change. `residueEquivalence_functor_obj_hom` identifies the
forward structural map with `pullback.snd`. The reassociated theorem
`residueEquivalence_functor_map_fst` records

```text
(B.map f).left ≫ pullback.fst = pullback.fst ≫ f.left.
```

Thus the categorical reconstruction introduces auxiliary finite covers only
inside the proof of fullness. The public equivalence retains the original
covers, the native residue homomorphism, and the native pullback maps.
