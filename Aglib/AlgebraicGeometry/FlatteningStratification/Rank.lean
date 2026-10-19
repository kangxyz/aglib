/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.LocallyFree
public import Aglib.RingTheory.FittingIdeal.Stratification

/-!
# The rank stratification by Fitting ideals

Let `F` be a quasi-coherent `𝒪_S`-module of finite type on a scheme `S`. For `r : ℕ`, the
**rank-`r` Fitting stratum** `rankStratum F hF r` is the locally closed subscheme
`V(Fitt_{r-1}(F)) \ V(Fitt_r(F))` of `S`, with the convention `Fitt_{-1}(F) = 0`
(`fittingIdealSheafPred`): the open subscheme of the closed subscheme `V(Fitt_{r-1}(F))`
complementary to `V(Fitt_r(F))`. Its immersion is `rankStratumι F hF r`.

* `exists_lift_rankStratumι_iff`: a morphism `g : T ⟶ S` factors through the stratum if and only if
  `Fitt_k(F)` pulls back to `0` for `k < r` and `Fitt_r(F)` pulls back to the unit ideal sheaf.
* `exists_lift_rankStratumι_iff_fittingIdealSheaf`: when `g^* F` is of finite type (for instance
  when `F` is of finite presentation), equivalently `Fitt_k(g^* F) = 0` for `k < r` and
  `Fitt_r(g^* F) = 𝒪_T` (Stacks Project, Tag 0C3D, for the base change).
* `exists_lift_rankStratumι_iff_stalkwise`: equivalently, for all affine opens `V ⊆ g ⁻¹ U` with
  `U` affine, every localization of `Γ(T, V) ⊗_{Γ(S, U)} Γ(F, U)` at a prime is free of rank `r`
  (the algebraic criterion `Module.fittingIdeal_map_eq_bot_and_eq_top_iff`, Stacks, Tag 07ZD in
  stalkwise form). This is the form of Stacks, Tag 05P8 (3) for `F` of finite type.
* `exists_lift_rankStratumι_iff_sheafHasRank`: for `F` of finite presentation, `g` factors through
  the stratum if and only if `g^* F` is finite locally free of constant rank `r`
  (`Scheme.Modules.SheafHasRank`); this is the finite-presentation case of Stacks Project,
  Tag 05P8 (Lemma 31.9.6) (3), the stratum `Z_{r-1} \ Z_r` representing local freeness of rank
  `r`. Finite presentation stands in for the finite type of `g^* F`, which Aglib does not yet
  derive from finite type of `F`.
* `mem_support_fittingIdealSheafPred_iff`: a point lies in the support of `Fitt_{r-1}(F)` if and
  only if the fibre of `F` there has dimension at least `r`.

This is the case `n = 0` of the flattening stratification (Nitsure, *Construction of Hilbert and
Quot schemes*, arXiv:math/0504590v1, Theorem 4.3, pp. 19–20), where the stratum is cut out by
Fitting ideals rather than by Nitsure's local minimal presentations. The flatness functor of the
disjoint union of the strata (Stacks, Tag 05P9, which needs finite presentation, Tag 0FJ0) is not
formalized here.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {S T : Scheme.{u}} (F : S.Modules) (hF : QuasiCoherent.affineLocallyFiniteType S F)

/-- `Fitt_{r-1}(F)`, with the convention `Fitt_{-1}(F) = 0`. -/
def fittingIdealSheafPred : ℕ → S.IdealSheafData
  | 0 => ⊥
  | r + 1 => fittingIdealSheaf F hF r

/-- The rank-`r` Fitting stratum `V(Fitt_{r-1}(F)) \ V(Fitt_r(F))` of `S`. -/
abbrev rankStratum (r : ℕ) : Scheme.{u} :=
  IdealSheafData.locallyClosed (fittingIdealSheafPred F hF r) (fittingIdealSheaf F hF r)

/-- The immersion of the rank-`r` Fitting stratum into `S`. -/
def rankStratumι (r : ℕ) : rankStratum F hF r ⟶ S :=
  IdealSheafData.locallyClosedι _ _

instance (r : ℕ) : IsImmersion (rankStratumι F hF r) := by
  unfold rankStratumι
  infer_instance

/-- The predecessor Fitting ideal pulls back to zero exactly when all `Fitt_k`, `k < r`, do. -/
theorem comap_fittingIdealSheafPred_eq_bot_iff (g : T ⟶ S) (r : ℕ) :
    (fittingIdealSheafPred F hF r).comap g = ⊥ ↔
      ∀ k < r, (fittingIdealSheaf F hF k).comap g = ⊥ := by
  cases r with
  | zero => simp [fittingIdealSheafPred]
  | succ r =>
    refine ⟨fun h k hk => le_bot_iff.mp ?_, fun h => h r r.lt_succ_self⟩
    rw [← h]
    exact IdealSheafData.comap_mono g (fittingIdealSheaf_mono F hF (Nat.lt_succ_iff.mp hk))

/-- **Universal property of the Fitting stratum.** A morphism `g : T ⟶ S` factors through the
rank-`r` stratum if and only if `Fitt_k(F)` pulls back to zero for `k < r` and `Fitt_r(F)` pulls
back to the unit ideal sheaf. -/
theorem exists_lift_rankStratumι_iff (g : T ⟶ S) (r : ℕ) :
    (∃ g' : T ⟶ rankStratum F hF r, g' ≫ rankStratumι F hF r = g) ↔
      (∀ k < r, (fittingIdealSheaf F hF k).comap g = ⊥) ∧
        (fittingIdealSheaf F hF r).comap g = ⊤ := by
  rw [rankStratumι, IdealSheafData.exists_lift_locallyClosedι_iff,
    comap_fittingIdealSheafPred_eq_bot_iff]

/-- The universal property in terms of the Fitting ideal sheaves of `g^* F` (Stacks Project,
Tag 0C3D). -/
theorem exists_lift_rankStratumι_iff_fittingIdealSheaf (g : T ⟶ S)
    (hgF : QuasiCoherent.affineLocallyFiniteType T ((pullback g).obj F)) (r : ℕ) :
    (∃ g' : T ⟶ rankStratum F hF r, g' ≫ rankStratumι F hF r = g) ↔
      (∀ k < r, fittingIdealSheaf ((pullback g).obj F) hgF k = ⊥) ∧
        fittingIdealSheaf ((pullback g).obj F) hgF r = ⊤ := by
  simp only [exists_lift_rankStratumι_iff, fittingIdealSheaf_comap g F hF hgF]

/-- **Universal property of the Fitting stratum, stalkwise form** (Stacks Project, Tags 07ZA (3)
and 07ZD, freeness in stalkwise form): `g : T ⟶ S` factors through the rank-`r` stratum if and only
if, for all affine opens `U` of `S` and `V ≤ g ⁻¹ᵁ U` of `T`, every localization of
`Γ(T, V) ⊗[Γ(S, U)] Γ(F, U)` at a prime of `Γ(T, V)` is free of rank `r`. -/
theorem exists_lift_rankStratumι_iff_stalkwise (g : T ⟶ S) (r : ℕ) :
    (∃ g' : T ⟶ rankStratum F hF r, g' ≫ rankStratumι F hF r = g) ↔
      ∀ (U : S.affineOpens) (V : T.affineOpens) (h : V.1 ≤ g ⁻¹ᵁ U.1),
        letI := (g.appLE U V h).hom.toAlgebra
        ∀ q : PrimeSpectrum Γ(T, V),
          q ∈ Module.freeLocus Γ(T, V) (Γ(T, V) ⊗[Γ(S, U)] Γ(F, U)) ∧
            Module.rankAtStalk (Γ(T, V) ⊗[Γ(S, U)] Γ(F, U)) q = r := by
  rw [exists_lift_rankStratumι_iff]
  simp only [IdealSheafData.comap_eq_bot_iff_forall, IdealSheafData.comap_eq_top_iff_forall,
    ideal_fittingIdealSheaf]
  constructor
  · rintro ⟨h0, h1⟩ U V h
    let := (g.appLE U V h).hom.toAlgebra
    have := QuasiCoherent.finite_sections_of_affineLocallyFiniteType F hF U
    exact (Module.fittingIdeal_map_eq_bot_and_eq_top_iff Γ(T, V)).mp
      ⟨fun k hk => h0 k hk U V h, h1 U V h⟩
  · intro H
    refine ⟨fun k hk U V h => ?_, fun U V h => ?_⟩
    · let := (g.appLE U V h).hom.toAlgebra
      have := QuasiCoherent.finite_sections_of_affineLocallyFiniteType F hF U
      exact ((Module.fittingIdeal_map_eq_bot_and_eq_top_iff Γ(T, V)).mpr (H U V h)).1 k hk
    · let := (g.appLE U V h).hom.toAlgebra
      have := QuasiCoherent.finite_sections_of_affineLocallyFiniteType F hF U
      exact ((Module.fittingIdeal_map_eq_bot_and_eq_top_iff Γ(T, V)).mpr (H U V h)).2

/-- **Universal property, finite local bases** (one direction): if `F` is of finite presentation and
`g^* F` is finite locally free of constant rank `r` (`SheafHasRank`), then `g` factors through the
rank-`r` stratum. -/
theorem exists_lift_rankStratumι_of_sheafHasRank [F.IsFinitePresentation] (g : T ⟶ S) (r : ℕ)
    (h : SheafHasRank ((pullback g).obj F) r) :
    ∃ g' : T ⟶ rankStratum F hF r, g' ≫ rankStratumι F hF r = g :=
  (exists_lift_rankStratumι_iff_fittingIdealSheaf F hF g
    (QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation g F) r).mpr
    (fittingIdealSheaf_eq_of_sheafHasRank _ _ h)

/-- If `g` factors through the rank-`r` stratum of a finitely presented `F`, every fibre of
`g^* F` has dimension `r`. -/
theorem sheafRank_pullback_eq_of_exists_lift [F.IsFinitePresentation] (g : T ⟶ S) (r : ℕ)
    (h : ∃ g' : T ⟶ rankStratum F hF r, g' ≫ rankStratumι F hF r = g) (y : T) :
    sheafRank ((pullback g).obj F) y = r := by
  obtain ⟨h0, h1⟩ := (exists_lift_rankStratumι_iff_fittingIdealSheaf F hF g
    (QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation g F) r).mp h
  exact sheafRank_eq_of_fittingIdealSheaf _ _ h0 h1 y

/-- **Universal property of the Fitting stratum** (Nitsure, arXiv:math/0504590v1, Theorem 4.3, case
`n = 0`; the finite-presentation case of Stacks Project, Tag 05P8 (Lemma 31.9.6) (3), with
Tag 0C3G (Lemma 31.9.5)): for `F` of finite presentation, a morphism `g : T ⟶ S` factors through
the rank-`r` stratum if and only if `g^* F` is finite locally free of constant rank `r`. For `F`
of finite type see `exists_lift_rankStratumι_iff_stalkwise`. -/
theorem exists_lift_rankStratumι_iff_sheafHasRank [F.IsFinitePresentation] (g : T ⟶ S) (r : ℕ) :
    (∃ g' : T ⟶ rankStratum F hF r, g' ≫ rankStratumι F hF r = g) ↔
      SheafHasRank ((pullback g).obj F) r := by
  rw [exists_lift_rankStratumι_iff_fittingIdealSheaf F hF g
    (QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation g F) r]
  exact fittingIdealSheaf_eq_bot_and_eq_top_iff_sheafHasRank _ _ r

/-- A point lies in the support of `Fitt_{r-1}(F)` (with `Fitt_{-1} = 0`) if and only if the fibre
of `F` there has dimension at least `r`. -/
theorem mem_support_fittingIdealSheafPred_iff {S : Scheme.{u}} (F : S.Modules)
    [F.IsFinitePresentation] (hF : QuasiCoherent.affineLocallyFiniteType S F) (y : S) (r : ℕ) :
    y ∈ (fittingIdealSheafPred F hF r).support ↔ r ≤ sheafRank F y := by
  cases r with
  | zero => exact iff_of_true (Set.mem_univ y) (Nat.zero_le _)
  | succ r =>
    change y ∈ (fittingIdealSheaf F hF r).support ↔ _
    rw [← not_iff_not, ← sheafRank_le_iff_notMem_support F hF y r, not_le]
    exact Nat.lt_succ_iff.symm

end AlgebraicGeometry.Scheme.Modules
