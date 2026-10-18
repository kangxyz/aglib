# Flattening stratification

Plan row F12: the flattening stratification of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Theorem 4.3 (pp. 19–23). This family covers the case `n = 0`, the
stratification of a scheme by the local rank of a quasi-coherent sheaf of finite type, with the
strata cut out by Fitting ideal sheaves instead of Nitsure's local minimal presentations, and the
rank strata of families of sheaves used in the general case: the joint strata `W_{e_0, …, e_n}`
and the refined strata `S_f` of pp. 21–22, in the form of universal properties for the ranks of
given sheaves `E_i`. The general case `n > 0` itself is not assembled here.

## Prerequisites and consumers

- Lower prerequisites: [Fitting ideal sheaves](../Modules/FittingIdeal/README.md) (including
  `Scheme.Modules.fittingIdealSheaf_eq_top_of_sheafRank_le` and
  `Scheme.Modules.isClosed_setOf_le_sheafRank`), the locally closed subschemes and pullback
  criteria of [IdealSheaf/LocallyClosed](../IdealSheaf/LocallyClosed.lean)
  (`Scheme.IdealSheafData.comap_iSup_eq_bot_iff`,
  `Scheme.IdealSheafData.comap_finset_prod_eq_top_iff`), the wide-pullback factorizations of
  [Limits/Shapes/WidePullbacks](../../CategoryTheory/Limits/Shapes/WidePullbacks.lean) and the
  algebraic criterion `Module.fittingIdeal_map_eq_bot_and_eq_top_iff` of
  [RingTheory/FittingIdeal/Stratification](../../RingTheory/FittingIdeal/Stratification.lean).
- Present consumers: the tests `AglibTest.AlgebraicGeometry.FlatteningStratification.Rank`,
  `.Universal`, `.Coproduct`, `.Finite` and `.Closed`.

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

[Coproduct](Coproduct.lean), for `F` of finite presentation:

- `rankStrataι F hF : ∐ r, S_r ⟶ S` packages the strata as one morphism. It is a monomorphism
  (`rankStrataι_mono`, an instance), and `g : T ⟶ S` factors through it iff `g^* F` is finite
  locally free (`exists_lift_rankStrataι_iff`). This is Stacks, Tag 05P9, and Nitsure's
  Theorem 4.3 (ii) for `n = 0`, in the locally free form: Stacks represents the flatness functor,
  and flat ⇔ finite locally free for finitely presented sheaves (Tag 05P2) is not formalized.
  `rankStrataι F hF` is in general not an immersion; the source carries the disjoint union
  topology.

[Finite](Finite.lean), for finitely many finitely presented `E_j`, `j ∈ J`:

- `jointRankStratum E hE e`, the wide pullback over `S` of the strata `rankStratum (E j) _ (e j)`,
  is Nitsure's `W_{e_0, …, e_n}` (pp. 21–22, built there by iterating the case `n = 0`):
  `exists_lift_jointRankStratumι_iff` says `g` factors through it iff every `g^* E_j` is finite
  locally free of constant rank `e j`.
- `jointRankStrataι E hE`, the wide pullback of the morphisms `rankStrataι (E j) _`, is a
  monomorphism (`jointRankStrataι_mono`, an instance) along which `g` factors iff every `g^* E_j`
  is finite locally free (`exists_lift_jointRankStrataι_iff`).

[Closed](Closed.lean), for a family `E_i`, `i ∈ I` of any size, of finitely presented sheaves:

- `exists_lift_closedJointRankStratumι_iff`: if the fibre dimensions of `E_i` are bounded by `e_i`,
  the closed subscheme `V(⨆_i Fitt_{e_i - 1}(E_i))` represents the morphisms `g` along which every
  `g^* E_i` is finite locally free of rank `e_i`.
- `exists_lift_refinedJointRankStratumι_iff`: the refined stratum, the closed condition
  `⨆_i Fitt_{e_i - 1}(E_i)` on the open complement of `⋃_{j ∈ J₀} V(Fitt_{e_j}(E_j))` for a finite
  `J₀`, represents the same condition under the hypothesis that every point at which the `E_j`,
  `j ∈ J₀`, have fibre dimensions `e_j` has fibre dimensions `≤ e_i` for all `i`. This is Nitsure's
  `S_f` (p. 22) with `E_i = π_* F(N + i)` and `J₀ = {0, …, n}`; the hypothesis is the consequence
  of (B), (C) and `deg P_s ≤ n` derived on p. 22, with `=` weakened to `≤`, and is not statement
  (C) itself. Its discharge for Nitsure's `F` is open.
- `closure_range_rankStratumι_subset`: the closure of the image of `S_r` lies in the union of the
  images of the `S_{r'}`, `r' ≥ r`; this is Nitsure's Theorem 4.3 (iii) for `n = 0`.

## Not covered

- The flatness form of the universal property: flat ⇔ finite locally free for finitely presented
  sheaves (Stacks, Tag 05P2) is not formalized, so the results above are stated for finite local
  freeness. For modules of finite type only, `⊔_r S_r ⟶ S` does not represent flatness (Stacks,
  Tag 0FJ0).
- The general case `n > 0` of Theorem 4.3 (Nitsure, pp. 20–23): the strata `S_f` for Nitsure's
  `E_i = π_* F(N + i)` on a non-affine base, the discharge of the hypothesis of
  `exists_lift_refinedJointRankStratumι_iff`, the universal property (ii) and the closure
  property (iii) for `n > 0`, and the finiteness of the set of Hilbert polynomials as part of the
  stratification.
