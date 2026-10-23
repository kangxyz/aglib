# Japanese domains and Nagata rings

Import `Aglib.RingTheory.Nagata.Defs`.

For a commutative domain `R : Type u`, `IsJapaneseRing.{u, v} R` is the
Japanese, or N-2, property of
[Stacks, Definition 10.161.1](https://stacks.math.columbia.edu/tag/0BI1).
It tests every field `L : Type (max u v)` with an algebra structure over
the canonical `FractionRing R` and finite dimension over that field. Its
conclusion is the actual

```text
Module.Finite R (integralClosure R L).
```

The `Algebra R L` action is supplied together with
`IsScalarTower R (FractionRing R) L`, so the coefficient map is the
original map through the canonical fraction field. There is no
separability assumption. Japanese domains need not be Noetherian;
Noetherianity is not built into this predicate.

For any commutative ring R, `IsNagataRing.{u, v} R` is the conjunction of
Noetherianity and `IsJapaneseRing.{u, v} (R ⧸ p)` for every prime ideal p,
as in [Stacks, Definition 10.162.1](https://stacks.math.columbia.edu/tag/032E).
The prime quotient uses its original ring and its canonical fraction
field; it need not be normal. These are explicit propositions, following
the pattern of the [excellence predicates](../Excellent/Defs.lean).

`IsJapaneseRing.finite_integralClosure` exposes the original finiteness
conclusion. `IsNagataRing.isNoetherianRing` and
`IsNagataRing.isJapaneseRing_quotient` expose the two Nagata components.

The auxiliary universe v is part of both interfaces. It selects extension
fields in `Type (max u v)` and remains unchanged when passing to a prime
quotient. No invariance under changing v, and no transfer from a different
chosen fraction field, is asserted here.

The first concrete consumer is
[complete normal local surfaces](CompleteSurface.md), which proves the
Nagata property using normalization finiteness for every actual prime
quotient. The equivalence with the Noetherian universally Japanese
condition and stability under finite type, as in
[Stacks, Proposition 10.162.15](https://stacks.math.columbia.edu/tag/0334),
are separate mathematical obligations. Neither that stability nor
normalization of finite-type graph algebras is a premise hidden in these
definitions.
