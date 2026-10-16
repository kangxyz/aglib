# Actual derived direct image of ordinary closed descent

[Descent](Descent.lean) gives
`Scheme.Modules.closedImmersionDerivedDescentIso i f M hM n` for a closed
immersion `i : Z ⟶ X`, an arbitrary morphism `f : X ⟶ S`, and an actual
module sheaf `M` annihilated by `i.ker`. It identifies the installed native
`Rf(single_n M)` with `R(i ≫ f)(single_n (i* M))` for every integer `n`.
The coefficient on the closed source is the original ordinary pullback.
Quasicoherence, Noetherianity and finiteness are unnecessary here.

The isomorphism is the explicit composite of original closed descent,
the installed exact-single comparison for closed pushforward, and the
original geometric derived-composition comparison. Its forward map starts
with the original geometric adjunction unit.
`closedImmersionDerivedDescentIso_hom` gives the literal factorization;
`closedImmersionDerivedDescentIso_hom_unit` gives its original unit square.
The existing exact-single and composition APIs retain their respective
installed derived units. The source uses their standard native derived
universe `u + 1`, without choosing another derived model.

Ordinary closed pushforward is exact. This result does not assert derived
full faithfulness or identify ordinary pullback with derived pullback.
The coherent positive-thickening supplier in
`Modules/ClosedImmersion/CoherentSupport` can feed this same comparison
directly into closed-support induction in the actual D-plus target.

The source passed with receipt `1792116968631488000-64887` in 2.9 seconds
at the default budget. `ClosedDerivedDescentConsumer.lean` passed with
receipt `1792117034195198000-65946`, checking the actual derived objects
and original unit formulas for arbitrary schemes and integer singles.
All three inspected declarations use only the three standard axioms.
