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

The source scheme is already regular. This interface does not remove a
divisorial part of an arbitrary ideal, extend a given rational map, construct
common regular domination or resolve an initially singular scheme. The
[original rational-coordinate ideals](../../RationalMap/BaseIdeal.md) are a
separate provider with their own normalization and dimension hypotheses.
