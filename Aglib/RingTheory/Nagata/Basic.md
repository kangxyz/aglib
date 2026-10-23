# Japanese rings and the original coefficient maps

Import `Aglib.RingTheory.Nagata.Basic`.

The interfaces use the existing `IsJapaneseRing.{u, 0}` and
`IsNagataRing.{u, 0}` predicates. All rings and fields are in `Type u`.
The auxiliary test universe is exactly zero; no invariance under changing
that parameter is assumed.

`IsJapaneseRing.finite_integralClosure_of_isFractionRing` accepts any
supplied fraction field K of R and a finite extension L/K. It retains
the same L, the original R-action on L, and the literal conclusion

```text
Module.Finite R (integralClosure R L).
```

The canonical localization equivalence `FractionRing R ≃ₐ[R] K`
defines an action of `FractionRing R` on the same L. Its restriction to R
is proved to be the original action, and finite dimension is transported
along the field equivalence. The Japanese definition then applies directly.
There is no separability or Noetherianity hypothesis.

`IsJapaneseRing.of_ringEquiv` transports the Japanese property through an
actual ring equivalence `R ≃+* S`. For each original S-extension L, the
proof restricts coefficients through that equivalence. The same
`FractionRing S` is a fraction field of R, using its canonical localization
action inherited from R -> S throughout. The already proved
[`integralClosure.equivOfIntegral`](../IntegralClosure/FiniteOverNormal.md)
compares the two literal closures by the identity on ambient elements.
Finite generation transfers to S without changing L or its S-action.

`IsNagataRing.isJapaneseRing` applies this transport to
`RingEquiv.quotientBot R`. The Nagata predicate first supplies Japanese
`R ⧸ (⊥ : Ideal R)`; the proof returns to R through that equivalence,
rather than treating the actual quotient as definitionally equal to R.

These are the coefficient and zero-prime bridges for
[finite ascent](Finite.md). They use the standard Japanese and Nagata
definitions from [Stacks 10.161.1](https://stacks.math.columbia.edu/tag/0BI1)
and [10.162.1](https://stacks.math.columbia.edu/tag/032E).
Finite-type or localization stability is not asserted here.
