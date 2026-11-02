# Intrinsic Gorensteinness and the same normal-quotient canonical module

Let `q:P→S` be the original surjective local map, with `P` regular local,
`S` a normal Noetherian local domain, `dim P=n+r`, and `dim S=r≤2`.
Let `K` be the same degree-`n` homology of the installed derived coinduction
of the regular `P` module.

`coinducedHomologyLinearEquivOfNormalQuotient` constructs an actual
`S`-linear frame `K ≃ S` from native `injdim_S(S)≤d` for any finite bound
`d`. Finiteness over this original ambient ring follows from the actual
surjection. The existing normal-quotient concentration theorem supplies
the full off-degree Ext vanishing; the canonical-module theorem proves
the frame from intrinsic self-injective dimension, without assuming a
regular-sequence kernel, homothety, projectivity, or desired triviality.

The `OfIso` variant handles an actual ambient coefficient-line frame by
the original derived-coinduction and homology maps.

`exists_self_hasInjectiveDimensionLE_iff_nonempty_coinducedHomologyLinearEquiv`
proves the honest equivalence

`(∃ d, injdim_S(S)≤d) ↔ Nonempty (K ≃ₗ[S] S)`.

The forward implication is the new frame construction. The reverse
implication reuses the unchanged original normal-quotient theorem and
in fact gives the bound `r`. No replacement Gorenstein predicate is
introduced. The selected ambient Ext and both derived-category universes
remain independent. There is no completion assumption, and no later
stalk is declared finite over an earlier Cohen base.

This is an algebraic statement about the actual selected module. A
geometric canonical-stalk identification, sheaf-local triviality, or an
exceptional-curve dualizing-line comparison must still be supplied by
the original geometric interfaces; they are not inferred from names.
