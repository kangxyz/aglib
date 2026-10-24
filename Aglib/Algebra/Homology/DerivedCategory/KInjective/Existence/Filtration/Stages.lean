/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Filtration.Growth
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Filtration.Union
public import Mathlib.Order.TransfiniteIteration

/-!
# The actual continuous acyclic subobject stages

Native transfinite iteration is applied to the total inflationary growth
operator. Only the resulting increasing stages, not arbitrary acyclic
subobjects, are combined at limits. Their full predecessor diagrams are retained.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian
  HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G) (M : CochainComplex C ℤ) (hM : M.Acyclic)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The actual native subobject at each well-ordered stage. -/
def acyclicStages (j : J) : Subobject M :=
  transfiniteIterate (acyclicGrowth hG M hM) j ⊥

lemma acyclicStages_monotone : Monotone (acyclicStages hG M hM (J := J)) :=
  monotone_transfiniteIterate _ _ (le_acyclicGrowth hG M hM)

/-- The coherent diagram of all stage inclusions into the original complex. -/
def acyclicStagesFunctor : J ⥤ MonoOver M :=
  (acyclicStages_monotone hG M hM).functor ⋙ Subobject.representative

/-- The entire strict predecessor diagram, not merely successor maps. -/
def acyclicPredecessors (j : J) : Set.Iio j ⥤ MonoOver M :=
  (show Monotone (fun x : Set.Iio j ↦ x.val) from fun _ _ h ↦ h).functor ⋙
    acyclicStagesFunctor hG M hM

lemma acyclicStages_bot : acyclicStages hG M hM (⊥ : J) = ⊥ :=
  transfiniteIterate_bot _ _

omit [OrderBot J] in
lemma acyclicStages_succ (j : J) (hj : ¬ IsMax j) :
    acyclicStages hG M hM (Order.succ j) =
      acyclicGrowth hG M hM (acyclicStages hG M hM j) :=
  transfiniteIterate_succ _ _ _ hj

lemma acyclicStages_limit (j : J) (hj : Order.IsSuccLimit j) :
    acyclicStages hG M hM j = diagramSup (acyclicPredecessors hG M hM j) := by
  rw [acyclicStages, transfiniteIterate_limit _ _ _ hj]
  change (⨆ x : Set.Iio j, acyclicStages hG M hM x.val) =
    ⨆ x : Set.Iio j, Subobject.mk (acyclicStages hG M hM x.val).arrow
  simp only [Subobject.mk_arrow]

/-- Every stage is acyclic, by successor exactness and filtered unions. -/
lemma acyclicStages_acyclic (j : J) :
    (acyclicStages hG M hM j : CochainComplex C ℤ).Acyclic := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    rw [acyclicStages_bot]
    exact HomologicalComplex.acyclic_of_isZero _
      ((isZero_zero (CochainComplex C ℤ)).of_iso Subobject.botCoeIsoZero)
  | succ j hj ih =>
    rw [acyclicStages_succ hG M hM j hj]
    exact acyclicGrowth_acyclic hG M hM _ ih
  | isSuccLimit j hj ih =>
    have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
    rw [acyclicStages_limit hG M hM j hj]
    exact diagramSup_acyclic (acyclicPredecessors hG M hM j)
      (fun x ↦ ih x.val x.property)

/-- The limit stage is isomorphic to the actual colimit of its full strict
predecessor diagram. This supplies the comparison used by Hom-complex continuity. -/
def acyclicStagesLimitIso (j : J) (hj : Order.IsSuccLimit j) :
    colimit (acyclicPredecessors hG M hM j ⋙ MonoOver.forget M ⋙ Over.forget M) ≅
      (acyclicStages hG M hM j : CochainComplex C ℤ) := by
  have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
  let F := acyclicPredecessors hG M hM j
  let e : colimit (F ⋙ MonoOver.forget M ⋙ Over.forget M) ≅
      (diagramSup F : CochainComplex C ℤ) :=
    (colimit.isColimit _).coconePointUniqueUpToIso (diagramSupIsColimit F)
  exact e ≪≫ eqToIso (congrArg (fun A : Subobject M ↦ (A : CochainComplex C ℤ))
    (acyclicStages_limit hG M hM j hj).symm)

end CochainComplex
