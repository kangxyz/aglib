# Finite normalization from the purely inseparable case

`integralClosure.finite_of_finite_purelyInseparable R K L hpure` proves
`Module.Finite R (integralClosure R L)` for a Noetherian domain `R`, a supplied
fraction field `K` of `R`, and a finite field extension `L/K`. The given maps
`R → K → L` must agree with the original `R`-algebra structure on `L`.
The premise `hpure` supplies finiteness of the literal integral closure of
`R` in every finite purely inseparable extension `F/K`, with its original
`R`-action and compatible scalar tower.

The universes of `R`, `K` and `L` may differ. The fields quantified by `hpure`
are in the universe of `L`. In particular, when all input types lie in
`Type u`, the premise tests `F : Type u`, matching the existing Japanese
condition at auxiliary universe zero. No change-of-universe result is used.

The proof embeds `L` in the actual finite normal closure `M` inside
`AlgebraicClosure L`. The field `F` fixed by every `K`-automorphism of `M`
is purely inseparable over `K`, and `M/F` is finite Galois. Thus
`B = integralClosure R F` is finite over `R` by `hpure`. This actual `B` is
normal, Noetherian and has fraction field `F`, even when `R` is not normal.
The existing trace-dual theorem gives finite `integralClosure B M` over `B`.
The comparison `integralClosure.equivOfIntegral R B M` retains each ambient
element and transfers finiteness to `integralClosure R M`. Finally the actual
embedding `L →ₐ[R] M` induces an injective linear map on the two literal
integral closures. Noetherianity of `R` gives finiteness of its source.

This is the general reduction used inside
`IntegralClosure/CompleteSurface.lean`, extracted without its local,
completion, dimension or original-base normality hypotheses. That existing
surface proof is unchanged. The current consumer is
[polynomial Japanese stability](../Nagata/Polynomial.md).

The lower inputs are `IntermediateField.isPurelyInseparable_fixedField_top`
in `FieldTheory/PurelyInseparable/FixedField.lean`, Mathlib's actual normal
closure and fixed-field Galois constructions, `IsIntegralClosure.finite`,
and the element-preserving `equivOfIntegral` in `FiniteOverNormal.lean`.
