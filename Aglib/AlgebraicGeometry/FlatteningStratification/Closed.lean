/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Universal

/-!
# Closed joint rank strata and closures of rank strata

Two consequences of the rank stratification by Fitting ideals for the proof of the flattening
stratification (Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1,
Theorem 4.3 and its proof, pp. 19–23).

* **Closed joint stratum** (proof of Theorem 4.3, p. 22, the subscheme `S_f ⊂ W_f`): let
  `(E_i)_{i ∈ I}` be any family of finitely presented sheaves on `S` whose fibre dimensions are
  bounded, `sheafRank (E i) y ≤ e i` for all `y`. Then the closed subscheme cut out by the ideal
  sheaf `⨆ i, Fitt_{e_i - 1}(E_i)` represents the morphisms `g` along which every `g^* E_i` is
  finite locally free of rank `e i` (`exists_lift_closedJointRankStratumι_iff`). Arbitrary
  suprema of quasi-coherent ideal sheaves exist, so no Noetherian stabilization is needed for this
  universal property; Nitsure uses the Noetherian hypothesis to see that the sum is coherent.
* **Refined joint stratum** (the subscheme `S_f ⊂ S` of p. 22 itself): for a finite set `J₀` of
  indices, the locally closed subscheme cut out by `⨆ i, Fitt_{e_i - 1}(E_i)` in the open
  complement of `⋃_{j ∈ J₀} V(Fitt_{e_j}(E_j))` represents the morphisms `g` along which every
  `g^* E_i` is finite locally free of rank `e i`, provided every point where the `E_j`, `j ∈ J₀`,
  have fibre dimensions `e j` has all fibre dimensions `≤ e i`
  (`exists_lift_refinedJointRankStratumι_iff`). In Nitsure's proof, `E_i = π_* F(N + i)` and
  `J₀ = {0, …, n}`. The hypothesis is not statement (C) itself: it is the consequence of
  statements (B) and (C) and of `deg P_s ≤ n` derived on p. 22 ("each `π_* F(N + i)` has fibres
  of constant rank `f(N + i)` on the subscheme `W_f`"), with `=` weakened to `≤`.
* **Closure of strata** (Theorem 4.3 (iii), case `n = 0`, p. 20): the closure of the image of the
  rank-`r` stratum lies in the union of the images of the strata of rank `≥ r`
  (`closure_range_rankStratumι_subset`), from the closedness of the loci of fibre dimension
  `≥ r` (`isClosed_setOf_le_sheafRank`, in `Modules/FittingIdeal/LocallyFree`).

The Fitting-ideal inputs `fittingIdealSheaf_eq_top_of_sheafRank_le` and
`isClosed_setOf_le_sheafRank` live in `Modules/FittingIdeal/LocallyFree`; the pullback criteria
`Scheme.IdealSheafData.comap_iSup_eq_bot_iff` and
`Scheme.IdealSheafData.comap_finset_prod_eq_top_iff` live in `IdealSheaf/LocallyClosed`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {S T : Scheme.{u}}

section Joint

variable {I : Type*} (E : I → S.Modules) (hE : ∀ i, QuasiCoherent.affineLocallyFiniteType S (E i))

/-- The ideal sheaf `⨆ i, Fitt_{e_i - 1}(E_i)` (with `Fitt_{-1} = 0`). -/
def closedJointRankIdeal (e : I → ℕ) : S.IdealSheafData :=
  ⨆ i, fittingIdealSheafPred (E i) (hE i) (e i)

/-- The closed joint rank stratum: the closed subscheme of `S` cut out by
`⨆ i, Fitt_{e_i - 1}(E_i)`. -/
abbrev closedJointRankStratum (e : I → ℕ) : Scheme.{u} :=
  (closedJointRankIdeal E hE e).subscheme

/-- The closed immersion of the closed joint rank stratum. -/
def closedJointRankStratumι (e : I → ℕ) : closedJointRankStratum E hE e ⟶ S :=
  (closedJointRankIdeal E hE e).subschemeι

instance (e : I → ℕ) : IsClosedImmersion (closedJointRankStratumι E hE e) := by
  unfold closedJointRankStratumι
  infer_instance

/-- **Universal property of the closed joint rank stratum** (Nitsure, arXiv:math/0504590v1, proof
of Theorem 4.3, p. 22, the subscheme `S_f` of `W_f`): if the fibre dimensions of the finitely
presented sheaves `E i` are bounded by `e i`, a morphism `g : T ⟶ S` factors through the closed
subscheme cut out by `⨆ i, Fitt_{e_i - 1}(E_i)` if and only if every `g^* E_i` is finite locally
free of constant rank `e i`. -/
theorem exists_lift_closedJointRankStratumι_iff [∀ i, (E i).IsFinitePresentation] (e : I → ℕ)
    (hrank : ∀ i y, sheafRank (E i) y ≤ e i) (g : T ⟶ S) :
    (∃ g' : T ⟶ closedJointRankStratum E hE e, g' ≫ closedJointRankStratumι E hE e = g) ↔
      ∀ i, SheafHasRank ((pullback g).obj (E i)) (e i) := by
  have key : ∀ J : S.IdealSheafData, J.comap g = ⊥ ↔ J ≤ (⊥ : T.IdealSheafData).map g :=
    fun J => le_bot_iff.symm.trans (IdealSheafData.map_gc g J ⊥)
  rw [closedJointRankStratumι, IdealSheafData.exists_lift_subschemeι_iff, key,
    closedJointRankIdeal, iSup_le_iff]
  refine forall_congr' fun i => ?_
  rw [← key, ← exists_lift_rankStratumι_iff_sheafHasRank (E i) (hE i) g (e i), rankStratumι,
    IdealSheafData.exists_lift_locallyClosedι_iff,
    fittingIdealSheaf_eq_top_of_sheafRank_le (E i) (hE i) (e i) (hrank i),
    IdealSheafData.comap_top]
  exact (and_iff_left rfl).symm

end Joint

section Refined

variable {I : Type*} (E : I → S.Modules) (hE : ∀ i, QuasiCoherent.affineLocallyFiniteType S (E i))

/-- The open condition of the refined joint stratum: the ideal sheaf
`∏_{j ∈ J₀} Fitt_{e_j}(E_j)`, whose support is `⋃_{j ∈ J₀} V(Fitt_{e_j}(E_j))`. -/
def refinedJointRankOpenIdeal (e : I → ℕ) (J₀ : Finset I) : S.IdealSheafData :=
  ∏ j ∈ J₀, fittingIdealSheaf (E j) (hE j) (e j)

/-- The refined joint rank stratum: the locally closed subscheme of `S` cut out by
`⨆ i, Fitt_{e_i - 1}(E_i)` in the complement of `⋃_{j ∈ J₀} V(Fitt_{e_j}(E_j))`. -/
abbrev refinedJointRankStratum (e : I → ℕ) (J₀ : Finset I) : Scheme.{u} :=
  IdealSheafData.locallyClosed (closedJointRankIdeal E hE e) (refinedJointRankOpenIdeal E hE e J₀)

/-- The immersion of the refined joint rank stratum. -/
def refinedJointRankStratumι (e : I → ℕ) (J₀ : Finset I) :
    refinedJointRankStratum E hE e J₀ ⟶ S :=
  IdealSheafData.locallyClosedι _ _

instance (e : I → ℕ) (J₀ : Finset I) : IsImmersion (refinedJointRankStratumι E hE e J₀) := by
  unfold refinedJointRankStratumι
  infer_instance

/-- **Universal property of the refined joint rank stratum** (Nitsure, arXiv:math/0504590v1, proof
of Theorem 4.3, p. 22, the subscheme `S_f`): let `J₀` be a finite set of indices such that every
point at which the `E_j`, `j ∈ J₀`, have fibre dimensions `e j` has `sheafRank (E i) y ≤ e i` for
all `i`. Then a morphism `g : T ⟶ S` factors through the refined joint rank stratum if and only if
every `g^* E_i` is finite locally free of constant rank `e i`. -/
theorem exists_lift_refinedJointRankStratumι_iff [∀ i, (E i).IsFinitePresentation]
    (e : I → ℕ) (J₀ : Finset I)
    (H : ∀ y : S, (∀ j ∈ J₀, sheafRank (E j) y = e j) → ∀ i, sheafRank (E i) y ≤ e i)
    (g : T ⟶ S) :
    (∃ g' : T ⟶ refinedJointRankStratum E hE e J₀, g' ≫ refinedJointRankStratumι E hE e J₀ = g) ↔
      ∀ i, SheafHasRank ((pullback g).obj (E i)) (e i) := by
  have hrank : ∀ i, SheafHasRank ((pullback g).obj (E i)) (e i) ↔
      (fittingIdealSheafPred (E i) (hE i) (e i)).comap g = ⊥ ∧
        (fittingIdealSheaf (E i) (hE i) (e i)).comap g = ⊤ := fun i => by
    rw [← exists_lift_rankStratumι_iff_sheafHasRank (E i) (hE i) g (e i), rankStratumι,
      IdealSheafData.exists_lift_locallyClosedι_iff]
  rw [refinedJointRankStratumι, IdealSheafData.exists_lift_locallyClosedι_iff,
    closedJointRankIdeal, IdealSheafData.comap_iSup_eq_bot_iff, refinedJointRankOpenIdeal,
    IdealSheafData.comap_finset_prod_eq_top_iff]
  constructor
  · rintro ⟨h0, h1⟩ i
    refine (hrank i).mpr ⟨h0 i, ?_⟩
    rw [← IdealSheafData.range_subset_compl_support_iff]
    rintro _ ⟨t, rfl⟩
    have hJ : ∀ j ∈ J₀, sheafRank (E j) (g t) = e j := fun j hj => by
      obtain ⟨g', hg'⟩ : ∃ g' : T ⟶ rankStratum (E j) (hE j) (e j),
          g' ≫ rankStratumι (E j) (hE j) (e j) = g := by
        rw [rankStratumι, IdealSheafData.exists_lift_locallyClosedι_iff]
        exact ⟨h0 j, h1 j hj⟩
      rw [← hg', Scheme.Hom.comp_apply]
      exact (mem_range_rankStratumι_iff (E j) (hE j) _ (e j)).mp ⟨_, rfl⟩
    exact (sheafRank_le_iff_notMem_support (E i) (hE i) (g t) (e i)).mp (H (g t) hJ i)
  · intro h
    exact ⟨fun i => ((hrank i).mp (h i)).1, fun j _ => ((hrank j).mp (h j)).2⟩

end Refined

/-- **Closure of the rank strata** (Nitsure, arXiv:math/0504590v1, Theorem 4.3 (iii), case `n = 0`,
p. 20): the closure of the image of the rank-`r` stratum lies in the union of the images of the
strata of rank at least `r`. -/
theorem closure_range_rankStratumι_subset (F : S.Modules)
    (hF : QuasiCoherent.affineLocallyFiniteType S F) [F.IsFinitePresentation] (r : ℕ) :
    closure (Set.range (rankStratumι F hF r)) ⊆
      ⋃ (r' : ℕ) (_ : r ≤ r'), Set.range (rankStratumι F hF r') := by
  have hU : (⋃ (r' : ℕ) (_ : r ≤ r'), Set.range (rankStratumι F hF r')) =
      {y : S | r ≤ sheafRank F y} := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, mem_range_rankStratumι_iff, exists_prop]
    exact ⟨fun ⟨r', hr', h⟩ => h ▸ hr', fun h => ⟨_, h, rfl⟩⟩
  rw [hU]
  refine closure_minimal ?_ (isClosed_setOf_le_sheafRank F hF r)
  rintro _ ⟨x, rfl⟩
  exact ((mem_range_rankStratumι_iff F hF _ r).mp ⟨x, rfl⟩).ge

end AlgebraicGeometry.Scheme.Modules
