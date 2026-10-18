# Flattening stratification

Plan row F12: the flattening stratification of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Theorem 4.3 (pp. 19–23). This family covers the case `n = 0`, the
stratification of a scheme by the local rank of a quasi-coherent sheaf of finite type, with the
strata cut out by Fitting ideal sheaves instead of Nitsure's local minimal presentations, and the
rank strata of families of sheaves used in the general case: the joint strata `W_{e_0, …, e_n}`
and the refined strata `S_f` of pp. 21–22, in the form of universal properties for the ranks of
given sheaves `E_i`. Over an affine Noetherian base `Spec A`, [HilbertPolynomial](HilbertPolynomial.lean)
and [Flatness](Flatness.lean) assemble the general case: the strata `S_f` and Theorem 4.3 (i),
(ii) for locally Noetherian test schemes, and (iii).

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
- Prerequisites of the general case: (B) and (C) for coherent `F` on `P^n_A`
  ([Cohomology/Projective/FiberBaseChange](../Cohomology/Projective/FiberBaseChange.lean)), the
  base-change comparison
  ([Cohomology/Projective/BaseChangeComparison](../Cohomology/Projective/BaseChangeComparison.lean)),
  the finiteness (A) and re-indexing of the fibre Hilbert polynomials
  ([Cohomology/Projective/HilbertPolynomial](../Cohomology/Projective/HilbertPolynomial/README.md)),
  Lemma 3.1 (`LargeTwistBaseChange`) and Lemma 3.2 (`FlatOfSections`), flatness local on the base
  ([Modules/Flat/Relative/LocalOnBase](../Modules/Flat/Relative/LocalOnBase.lean)) and
  factorization through monomorphisms ([Limits/Monomorphisms](../Limits/Monomorphisms.lean)).
- Present consumers: the tests `AglibTest.AlgebraicGeometry.FlatteningStratification.Rank`,
  `.Universal`, `.Coproduct`, `.Finite`, `.Closed`, `.HilbertPolynomial` and `.Flatness`.

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
- `mem_support_fittingIdealSheafPred_iff`: `y` lies in the support of `Fitt_{r-1}(F)` iff the fibre
  of `F` at `y` has dimension at least `r`.

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
  (C) itself. Over an affine Noetherian base it is discharged for Nitsure's `F`, for `f` that occurs
  and `N` a bound of the fibre statements of (B) and (C), by
  `exists_lift_hilbertPolynomialStratumι_iff` ([HilbertPolynomial](HilbertPolynomial.lean)).
  `mem_range_refinedJointRankStratumι_iff` describes the points of the refined stratum.
- `closure_range_rankStratumι_subset`: the closure of the image of `S_r` lies in the union of the
  images of the `S_{r'}`, `r' ≥ r`; this is Nitsure's Theorem 4.3 (iii) for `n = 0`.

[HilbertPolynomial](HilbertPolynomial.lean), over `Spec A` with `A` Noetherian, for
`e : ι ≃ Fin (n + 1)` and a coherent `F` on `P^n_A`, flat or not:

- `hilbertPolynomialStratum n e F hF N f` is Nitsure's `S_f` (p. 22): the refined joint stratum of
  `E_i = π_* F(N + i)`, `i ≥ 0`, with ranks `f(N + i)` and open conditions `J₀ = {0, …, n}`.
  It is Nitsure's stratum for `f` that occurs; for other `f` it can be nonempty.
- `IsFiberBaseChangeBound F N` contains the fibre statements of (B) and (C) beyond `N`: vanishing of
  the positive cohomology of every fibre of `F(d)` and bijectivity of every fibre base-change map
  in degree zero. It does not contain the vanishing of `H^r(P^n_A, F(d))`. Such `N` exists
  (`exists_isFiberBaseChangeBound`).
- For `N` such a bound and `d ≥ N`: the fibre rank of `π_* F(d)` at `y` is `P_y(d)`
  (`sheafRank_directImageTwist_eq_eval`); Theorem 4.3 (i), `|S_f| = {s | P_s = f}` for `f` that
  occurs (`range_hilbertPolynomialStratumι`; disjointness and covering:
  `iUnion_range_hilbertPolynomialStratumι_eq_univ_and_pairwiseDisjoint`); the universal property
  of `S_f` for `f` that occurs, `g` factors through `S_f` iff every `g^* π_* F(N + i)` is finite
  locally free of rank `f(N + i)` (`exists_lift_hilbertPolynomialStratumι_iff`); and
  Theorem 4.3 (iii) (`closure_range_hilbertPolynomialStratumι_subset`), with Nitsure's order
  `f ≤ g` as "`f(m) ≤ g(m)` for `m ≫ 0`".

[Flatness](Flatness.lean), in the same setting, for `N` a bound of the fibre statements of (B)
and (C):

- `hilbertPolynomialStrataι : ∐ S_f ⟶ Spec A`, `f` over the polynomials that occur, is a
  monomorphism (`mono_hilbertPolynomialStrataι`).
- Theorem 4.3 (ii) (`exists_lift_hilbertPolynomialStrataι_iff`): a morphism `g : T ⟶ Spec A` from a
  locally Noetherian `T` factors through `∐ S_f` iff the pullback of `F` to `P^n_A ×_{Spec A} T` is
  flat over `T`. "⇒" holds for every `T`
  (`relativeFlat_of_exists_lift_hilbertPolynomialStrataι`); flatness over each `S_f` and over
  `∐ S_f` is `relativeFlat_hilbertPolynomialStratum` and `relativeFlat_hilbertPolynomialStrata`.
- `exists_iso_hilbertPolynomialStrata`: the coproducts for two such bounds are isomorphic over
  `Spec A`. The componentwise independence of each `S_f` from `N` is not stated.
- The proof makes explicit two steps of Nitsure's printed proof: the comparison
  `φ^* π_* F(m) ≅ π_{T*} F_T(m)` for `m ≥ N`, proved affine-locally on locally Noetherian `T`
  (`moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_isFiberBaseChangeBound`, uniform
  in the test ring), and local constancy of the ranks of the locally free `g^* π_* F(N + j)`,
  `j ≤ n`, in place of local constancy of the Hilbert polynomial over `T`.

## Not covered

- The flatness form of the universal property: flat ⇔ finite locally free for finitely presented
  sheaves (Stacks, Tag 05P2) is not formalized, so the results above are stated for finite local
  freeness. For modules of finite type only, `⊔_r S_r ⟶ S` does not represent flatness (Stacks,
  Tag 0FJ0).
- The general case `n > 0` of Theorem 4.3 (Nitsure, pp. 20–23) over a non-affine base: the strata
  `S_f` and statements (i)–(iii) are proved here over an affine Noetherian base only.
- The converse direction of the universal property (ii) for test schemes that are not locally
  Noetherian, as Nitsure prints it; it needs cohomology and base change for flat families over
  arbitrary bases (citation needed).
