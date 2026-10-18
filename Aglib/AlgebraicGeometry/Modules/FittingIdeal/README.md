# Fitting ideal sheaves

Fitting ideal sheaves of quasi-coherent sheaves of finite type on arbitrary schemes, as Mathlib's
`Scheme.IdealSheafData`, after Stacks Project, Tag 0C3C (Section 31.9). Finite type is Aglib's
chart predicate `Scheme.Modules.QuasiCoherent.affineLocallyFiniteType`: on every affine chart the
restriction is quasi-coherent with finitely generated global sections. No Noetherian or
finite-presentation hypothesis enters the construction.

## Prerequisites and consumers

- Lower prerequisites: the algebraic [Fitting ideals](../../../RingTheory/FittingIdeal/README.md)
  (`Module.fittingIdeal`, base change and localization, `Module.fittingIdeal_extendScalars`,
  `Module.fittingIdeal_compHom_of_bijective`, `Module.finitePresentation_and_flat_of_forall_free`),
  the finite-type interface
  [QuasiCoherent/FiniteType/Sections](../QuasiCoherent/FiniteType/Sections.lean)
  (`QuasiCoherent.finite_sections_of_affineLocallyFiniteType`,
  `QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation`), the affine-open
  denominator clearing of
  [Localization/AffineOpenSections](../QuasiCoherent/Localization/AffineOpenSections.lean), the
  affine pullback-section comparison `affinePullbackGlobalSectionsIso`, the open-square comparison
  `pullbackOpenSquare` and the ideal-sheaf leaf
  [IdealSheaf/LocallyClosed](../../IdealSheaf/LocallyClosed.lean) (including
  `IdealSheafData.fromSpec_mem_support_iff`).
- Present consumers: the [flattening stratification](../../FlatteningStratification/README.md) and
  the tests `AglibTest.AlgebraicGeometry.Modules.FittingIdeal.Pullback` and
  `AglibTest.AlgebraicGeometry.FlatteningStratification.Rank`. The rank interface is Aglib's
  [LocallyFree/Rank](../LocallyFree/Rank.lean) (`SheafHasRank`, `sheafRank`).

## Main results

[Basic](Basic.lean):

- `Scheme.Modules.fittingIdeal_sections_basicOpen`: Fitting ideals of sections commute with
  restriction from `U` to a basic open `D(f)`; the restriction of sections is a localization at `f`
  and Fitting ideals commute with localization (Stacks, Tag 07ZA (3)).
- `Scheme.Modules.fittingIdealSheaf M hM k`, with `ideal_fittingIdealSheaf` (`rfl`): the ideal on an
  affine open `U` is `Module.fittingIdeal Γ(X, U) Γ(M, U) k`; `fittingIdealSheaf_mono`.

[Pullback](Pullback.lean):

- `Scheme.Modules.fittingIdeal_sections_pullback`: for affine opens `V ≤ g ⁻¹ᵁ U`,
  `Fitt_k(Γ(g^* F, V)) = Fitt_k(Γ(F, U)) Γ(T, V)` along `g.appLE U V`.
- `Scheme.Modules.fittingIdealSheaf_comap`: `(Fitt_k F).comap g = Fitt_k (g^* F)` for every morphism
  `g`, given finite type of `g^* F` as an argument (Stacks, Tags 07ZA (3) and 0C3D (Lemma 31.9.1)).
- The finite-type argument `hgF` on `g^* F` stands in for a theorem the library does not yet
  supply: the pullback of a quasi-coherent sheaf of finite type is of finite type. It is not a
  mathematical condition. Aglib provides it under `[F.IsFinitePresentation]`
  (`QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation`) or for a locally
  Noetherian `S` (`QuasiCoherent.affineLocallyFiniteType_pullback`). The
  `[IsFinitePresentation]` premises below serve the same purpose.

[LocallyFree](LocallyFree.lean):

- `Scheme.Modules.sheafRank_le_iff_notMem_support` (`[G.IsFinitePresentation]`): the fibre rank
  `sheafRank G y` is at most `k` iff `y ∉ V(Fitt_k(G))` (Stacks, Tag 07ZC (1) ⇔ (2), through
  `fittingIdealSheaf_comap` along `Spec κ(y) ⟶ T`); `sheafRank_eq_of_fittingIdealSheaf`;
  `sheafRank_pullback`: `sheafRank (f^* G) t = sheafRank G (f t)`.
- `Scheme.Modules.isFiniteLocallyFree_of_fittingIdealSheaf` (finite type only): the Fitting
  conditions `Fitt_k(G) = 0` (`k < r`), `Fitt_r(G) = 𝒪_T` give finite local freeness; on affine
  charts the sections are stalkwise free of rank `r`, hence finitely presented and flat
  (`Module.finitePresentation_and_flat_of_forall_free`, Stacks, Tag 00NX).
- `Scheme.Modules.fittingIdealSheaf_eq_of_sheafHasRank` and
  `fittingIdealSheaf_eq_bot_and_eq_top_iff_sheafHasRank` (finite type only): the Fitting
  conditions hold iff `SheafHasRank G r` (Stacks, Tag 0C3G, (1) ⇔ (2); algebraic form Tag 07ZD).
- The algebraic inputs are at their algebraic owners: `Module.fittingIdeal_compHom_of_bijective`
  and `Module.finitePresentation_and_flat_of_forall_free` in `RingTheory/FittingIdeal`,
  `Module.Finite.compHom_of_surjective` in
  [RingTheory/Finiteness/CompHom](../../../RingTheory/Finiteness/CompHom.lean), and Mathlib's
  `Module.rankAtStalk_eq` for the stalk rank as a fibre dimension.

## Not covered

- Stacks, Tags 0C3E (finite type of the Fitting ideals of a finitely presented module) and 0CYX
  (the closed subscheme cut out by `Fitt_0` and the support).
