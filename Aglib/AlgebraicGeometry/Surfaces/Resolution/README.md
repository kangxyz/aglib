# Principalization by finite point blowups

[Principalization](Principalization.md), in `Scheme.Blowup`, supplies
`exists_regular_pointBlowup_principalization` for a locally Noetherian integral
scheme `X` whose actual stalks are regular local rings of Krull dimension at
most two. The input is a nonzero native ideal sheaf `J` with an actual
Artinian quotient subscheme `J.subscheme`.

The result is a finite `PointBlowupChain` with actual composite `f : Y ⟶ X`.
It retains properness, dominance and `BirationalOver f (𝟙 X)`, integrality and
regularity of `Y`, and the same local dimension bound. Its conclusion
`cartierPullback J f` concerns local rank one of the actual ideal module of
`J.comap f`: the original total inverse-image ideal is Cartier.
`exists_regular_pointBlowup_principalization_of_dimension_le_two` accepts
`topologicalKrullDim X ≤ 2` and derives the required original stalk bounds.

[WeakTransform](WeakTransform.md) defines the weak ideal on an actual universal
blowup `B` as

```lean
(J.comap B.map).colon ((I.comap B.map) ^ r)
```

Here `I` is its actual centre ideal. Under `J ≤ I ^ r`, the exact equality
`(I.comap B.map) ^ r * B.weakTransform J r = J.comap B.map` retains the whole
inverse-image ideal. Its affine and stalk comparisons use the original
[ideal-sheaf colon](../../IdealSheaf/Colon.md) and the literal
[saturated-chart weak transform](../../../RingTheory/Blowup/WeakTransform.md).
The actual local-spectrum blowup comparison preserves this weak ideal and
the original local order.

The construction chooses closed points with two-dimensional local rings.
[Local colength](../../../RingTheory/Blowup/Colength.md) strictly decreases at
every new nonfree ideal stalk over the chosen centre. The finite multiset
`nonfreeIdealColengths` records those actual local lengths with multiplicity;
its well-founded decrease replaces the selected entry by finitely many smaller
entries and retains the entries away from the centre. It does not require a
decreasing unweighted sum. The principalization proof derives finite support and finite
local lengths from the actual Artinian quotient. Conversely, the
[actual-stalk Artinian bridges](../../IdealSheaf/Artinian.md) assemble finite
support and finite original stalk-quotient lengths into an Artinian weak
quotient along the chain.

At the terminal stage, every actual ideal stalk has a singleton basis. The
Cartier exceptional-power and product equations recover the original total
inverse-image ideal through the later dominant integral chain maps. This uses
the canonical ideal maps and Cartier avoidance; pullback of an abstract
invertible module alone is not substituted for the embedded ideal comparison.

## Supplied chains and their generic maps

[PointBlowupChain](PointBlowupChain.md), in `Scheme.Blowup.PointBlowupChain`,
concatenates supplied chains over their literal composite. For integral
original `X`, `functionFieldMap_isIso` and `functionFieldEquiv` identify
the original canonical function-field map of a supplied chain with an
isomorphism. This needs no additional regularity, Noetherianity,
properness or global dimension hypothesis.

[Trait](Trait.md) treats a supplied chain `f : Y ⟶ X` and an actual proper
`p : X ⟶ Spec R` over a DVR with specified fraction field `F`.
`PointBlowupChain.genericBaseChange_isIso` proves invertibility of the
literal `Over.pullback (baseMap R F)` image of `f`.
`PointBlowupChain.genericIso` has exactly that forward map, with the
original projection and base triangles. Regularity, integrality and
flatness of `X` are unnecessary for this preservation theorem. The separate
[proper section theorem](../../Morphisms/Proper/TraitSections.md) lifts
original sections through a proper map with such an invertible generic map.

Principalization starts with an already regular source and an Artinian
ideal quotient. The
[original rational-coordinate ideals](../../RationalMap/BaseIdeal.md)
supply such an ideal to
[projective extension](../../RationalMap/ProjectiveExtension.md), which in
turn serves [regular-source common domination](../Birational/CommonDomination.md).
Removing a divisorial part of an arbitrary ideal and resolving an initially
singular scheme remain separate obligations.
