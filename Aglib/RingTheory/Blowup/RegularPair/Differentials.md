# Differentials of the original regular-pair charts

For the original scalar tower `Λ → R → B` and actual chart
`B = Localization.Away.pairQuotient x y = R[T]/(x T - y)`,
`pairKaehlerEquiv` identifies the genuine `KaehlerDifferential Λ B` with

```text
((B ⊗[R] KaehlerDifferential Λ R) × B) /
  B · (T ⊗ dx - 1 ⊗ dy, image(x)).
```

The forward map sends `D(image(r))` to the class of `(1 ⊗ Dr, 0)` and
`D(T)` to the class of `(0,1)`. The inverse is the actual Kähler
base-change map on the first component, plus the second coefficient
times `D(T)`. These are maps on the given algebra, with its original
scalar action. The relation need not be a direct summand.

The underlying `IsAdjoinRoot.pairDifferentialEquiv` construction uses an
actual specified polynomial presentation, with both its original map
and root. A compatible coefficient derivation and root value lift to
the original algebra by its square-zero universal property. The two
inverse identities are proved on coefficient differentials and the
root differential. No smoothness, separability, freeness of the raw
differentials, or coefficient-field embedding is assumed.

Relative to `R`, `pairRelativeKaehlerEquiv` is the specialization of the
same presentation:

```text
KaehlerDifferential R B ≃ₗ[B] B/(image(x)),
D(T) ↦ 1,     D(image(r)) ↦ 0.
```

Its inverse sends the class of `b` to `b • D(T)`. The original relation
`image(y)=image(x) T` identifies `(image(x))` with the full inverse-image
point ideal when `x,y` are regular parameters. On the literal reciprocal
overlap, `pairReciprocal_D_coordinate` gives `D(T⁻¹)=-T⁻² • D(T)`.

`saturatedPairPresentation` transfers the actual polynomial presentation
through `pairChartEquiv`. The resulting `saturatedPairKaehlerEquiv` and
`saturatedPairRelativeKaehlerEquiv` therefore concern the original saturated
blowup algebra. Their hypotheses are exactly that `x` is a nonzerodivisor
on `R` and `y` is a nonzerodivisor on `R/(x)`. The transferred root is
the literal fraction `y/x`, and the coefficient map is the original one.

The current consumer is the ordinary point-blowup relative cotangent
calculation in the general surface comparison. Gluing the exceptional
cotangent line, reflexive determinant comparison, derived pushforward,
and proper trace are later obligations. In particular this leaf does
not assert an unconditional `E`-or-zero change for the reflexive
determinant of raw differentials.
