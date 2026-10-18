# Flattening stratification

Plan row F12: the flattening stratification of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Theorem 4.3 (pp. 19–20). This family presently covers the case `n = 0`, the
stratification of a scheme by the local rank of a quasi-coherent sheaf of finite type, with the
strata cut out by Fitting ideal sheaves instead of Nitsure's local minimal presentations.

## Prerequisites and consumers

- Lower prerequisites: [Fitting ideal sheaves](../Modules/FittingIdeal/README.md), the locally
  closed subschemes of [IdealSheaf/LocallyClosed](../IdealSheaf/LocallyClosed.lean) and the
  algebraic criterion `Module.fittingIdeal_map_eq_bot_and_eq_top_iff` of
  [RingTheory/FittingIdeal/Stratification](../../RingTheory/FittingIdeal/Stratification.lean).
- Present consumers: the tests `AglibTest.AlgebraicGeometry.FlatteningStratification.Rank` and
  `AglibTest.AlgebraicGeometry.FlatteningStratification.Universal`.

## Main results

[Rank](Rank.lean), for a quasi-coherent sheaf of finite type `F` on `S`:

- `Scheme.Modules.fittingIdealSheafPred F hF r`: `Fitt_{r-1}(F)` with `Fitt_{-1}(F) = 0`.
- `Scheme.Modules.rankStratum F hF r` and its immersion `rankStratumι F hF r`: the open subscheme of
  `V(Fitt_{r-1}(F))` complementary to `V(Fitt_r(F))`.
- `exists_lift_rankStratumι_iff`: `g : T ⟶ S` factors through the stratum if and only if
  `Fitt_k(F)` pulls back to zero for `k < r` and `Fitt_r(F)` pulls back to the unit ideal sheaf.
- `exists_lift_rankStratumι_iff_fittingIdealSheaf`: the same with the Fitting ideal sheaves of
  `g^* F` (given finite type of `g^* F`, for instance from finite presentation of `F`).
- `exists_lift_rankStratumι_iff_stalkwise`: equivalently, for all affine opens `V ≤ g ⁻¹ᵁ U`, every
  localization of `Γ(T, V) ⊗[Γ(S, U)] Γ(F, U)` at a prime is free of rank `r` (finite type only;
  the form of Stacks, Tag 05P8 (3) for finite type).
- `exists_lift_rankStratumι_iff_sheafHasRank` (`[F.IsFinitePresentation]`): `g` factors through the
  stratum iff `g^* F` is finite locally free of constant rank `r` (`Scheme.Modules.SheafHasRank`),
  the finite-presentation case of Stacks, Tag 05P8 (3). Finite presentation of `F` supplies finite
  type of `g^* F` and of its pullbacks to residue-field points; the Zariski-local freeness itself
  only uses finite type (`isFiniteLocallyFree_of_fittingIdealSheaf`). Corollaries:
  `exists_lift_rankStratumι_of_sheafHasRank` and `sheafRank_pullback_eq_of_exists_lift`.

The argument `hgF` (finite type of `g^* F`) and the `[F.IsFinitePresentation]` premises stand in
for a theorem the library does not yet supply: the pullback of a quasi-coherent sheaf of finite
type is of finite type. They are not mathematical conditions of the statements.

[Universal](Universal.lean), for `F` of finite presentation:

- `mem_range_rankStratumι_iff`: `y` lies in the image of `S_r` iff the fibre of `F` at `y` has
  dimension `r` (`Scheme.Modules.sheafRank`); the images of the strata partition `S`.
- `isFiniteLocallyFree_pullback_iff`: `g^* F` is finite locally free iff every point of `T` has an
  open neighbourhood `U` with `U ⟶ T ⟶ S` factoring through some `S_r` (the local form of Stacks,
  Tag 05P9, and of Nitsure's Theorem 4.3 for `n = 0`). That a finitely presented `g^* F` is
  finite locally free exactly when it is flat (Stacks, Tag 05P2) is not formalized here.

## Not covered

- The packaging of the strata as one morphism `⊔_r S_r ⟶ S` (a monomorphism representing the
  flatness functor of a finitely presented `F`, Stacks, Tag 05P9; false for finite type modules,
  Tag 0FJ0), and the general case `n > 0` (Nitsure, Lemmas 3.1–3.2 and pp. 19–21).
- Nitsure, Theorem 4.3 (iii), the closure of the strata.
