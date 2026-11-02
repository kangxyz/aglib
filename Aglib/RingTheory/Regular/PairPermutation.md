# Swapping regular pairs

`Aglib.RingTheory.Regular.PairPermutation` extends the native `IsSMulRegular`
namespace with two statements:

- `quotSMulTop_swap`: for a module `M` over a commutative ring `R`, if `x` and
  `y` are both regular on `M`, regularity of `y` on `QuotSMulTop x M` implies
  regularity of `x` on `QuotSMulTop y M`. Ring and module universes are independent.
- `proper_pair_swap_of_isDomain`: over a domain `R`, regularity of `x` on `R`,
  regularity of `y` on `R ⧸ Ideal.span {x}`, and properness of
  `Ideal.span {x, y}` imply regularity of `y` on `R` and regularity of `x` on
  `R ⧸ Ideal.span {y}`. No local-ring or Noetherian hypothesis is needed.

The module argument uses the public Mathlib identity
`IsSMulRegular.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul` and symmetry of
intersection and commuting scalar actions. It does not construct a separate
regular-sequence backend. In the domain specialization, properness makes the
first principal quotient nontrivial, so its regular scalar `y` is nonzero;
`IsSMulRegular.of_ne_zero` then supplies ambient regularity. Both principal
quotient comparisons use `Submodule.quotEquivOfEq` from the same equality
`r • (⊤ : Submodule R R) = Ideal.span {r}`.

The intended consumer is the one-pole raw chart/gluing construction in
`AlgebraicGeometry/Surfaces/RationalSingularities/IntegralTrace`. This leaf does
not alter those callers or the existing local Noetherian theorem
`RingTheory.Sequence.proper_regularPair_swap`, which also covers rings that are
not domains.
