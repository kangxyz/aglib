/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Rank

/-!
# The rank stratification flattens a finitely presented sheaf

Let `F` be a quasi-coherent `𝒪_S`-module of finite presentation. The rank strata `S_r` of
`Scheme.Modules.rankStratum` stratify `S` and flatten `F` universally, in the following local form
(Stacks Project, Tag 05P9 (Lemma 31.9.7); Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Theorem 4.3, case `n = 0`):

* `mem_range_rankStratumι_iff`: a point `y` lies in the image of `S_r` if and only if the fibre
  of `F` at `y` has dimension `r`; so the images of the strata partition `S`.
* `isFiniteLocallyFree_pullback_iff`: for `g : T ⟶ S`, the pullback `g^* F` is finite locally free
  (equivalently flat, `F` being finitely presented, Stacks Project, Tag 05P2 (Lemma 28.21.2); this
  equivalence is not formalized here) if and only if every point of `T` has an open neighbourhood
  `U` such that `U ⟶ T ⟶ S` factors through some stratum `S_r`.

The packaging of the strata as one morphism `⊔_r S_r ⟶ S` representing the flatness functor (a
monomorphism) is not part of this file.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {S T : Scheme.{u}} (F : S.Modules) (hF : QuasiCoherent.affineLocallyFiniteType S F)

/-- **The strata partition the base**: `y` lies in the image of the rank-`r` stratum if and only if
the fibre of `F` at `y` has dimension `r`. -/
theorem mem_range_rankStratumι_iff [F.IsFinitePresentation] (y : S) (r : ℕ) :
    y ∈ Set.range (rankStratumι F hF r) ↔ sheafRank F y = r := by
  rw [rankStratumι, IdealSheafData.range_locallyClosedι, Set.mem_sdiff, SetLike.mem_coe,
    SetLike.mem_coe]
  have h2 := sheafRank_le_iff_notMem_support F hF y r
  cases r with
  | zero =>
    simp only [fittingIdealSheafPred, IdealSheafData.support_bot]
    constructor
    · rintro ⟨-, hb⟩
      exact Nat.le_zero.mp (h2.mpr hb)
    · intro h
      exact ⟨Set.mem_univ y, h2.mp h.le⟩
  | succ r =>
    have h1 := sheafRank_le_iff_notMem_support F hF y r
    simp only [fittingIdealSheafPred]
    constructor
    · rintro ⟨ha, hb⟩
      have hle := h2.mpr hb
      have hnot : ¬sheafRank F y ≤ r := fun h => h1.mp h ha
      omega
    · intro h
      refine ⟨by_contra fun hc => ?_, h2.mp h.le⟩
      have := h1.mpr hc
      omega

/-- **Universal flattening, local form** (Stacks Project, Tag 05P9; Nitsure, Theorem 4.3, case
`n = 0`): for `F` of finite presentation and `g : T ⟶ S`, the pullback `g^* F` is finite locally
free if and only if every point of `T` has an open neighbourhood `U` such that `U ⟶ S` factors
through one of the rank strata. -/
theorem isFiniteLocallyFree_pullback_iff [F.IsFinitePresentation] (g : T ⟶ S) :
    IsFiniteLocallyFree T ((pullback g).obj F) ↔
      ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ r : ℕ, ∃ g' : U.toScheme ⟶ rankStratum F hF r,
        g' ≫ rankStratumι F hF r = U.ι ≫ g := by
  constructor
  · intro hfree t
    let r := sheafRank ((pullback g).obj F) t
    let U : T.Opens := ⟨{t' | sheafRank ((pullback g).obj F) t' = r},
      (sheafRank_locallyConstant ((pullback g).obj F)).isOpen_fiber r⟩
    refine ⟨U, rfl, r, ?_⟩
    rw [exists_lift_rankStratumι_iff_sheafHasRank]
    have e : (pullback (U.ι ≫ g)).obj F ≅ (restrictFunctor U.ι).obj ((pullback g).obj F) :=
      ((pullbackComp U.ι g).app F).symm ≪≫ (restrictFunctorIsoPullback U.ι).symm.app _
    have : IsFiniteLocallyFree U.toScheme ((pullback (U.ι ≫ g)).obj F) :=
      finiteLocallyFree_of_iso e.symm
    refine (sheafHasRank_iff_rank_eq _ r).mpr fun u => ?_
    rw [sheafRank_pullback, Scheme.Hom.comp_apply, ← sheafRank_pullback F g]
    exact u.2
  · intro H
    choose U hU r g' hg' using H
    refine finiteLocallyFree_of_openImmersionCover _ (fun t => (U t).toScheme) (fun t => (U t).ι)
      (fun t => ⟨t, ⟨t, hU t⟩, rfl⟩) fun t => ?_
    have hr : SheafHasRank ((pullback ((U t).ι ≫ g)).obj F) (r t) :=
      (exists_lift_rankStratumι_iff_sheafHasRank F hF _ (r t)).mp ⟨g' t, hg' t⟩
    have := hr.isFiniteLocallyFree
    exact finiteLocallyFree_of_iso
      (((pullbackComp (U t).ι g).app F).symm ≪≫ (restrictFunctorIsoPullback (U t).ι).symm.app _)

end AlgebraicGeometry.Scheme.Modules
