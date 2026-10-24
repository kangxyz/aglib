/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Filtration.Continuity

/-! # The actual successor quotients of the coherent acyclic filtration -/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G) (M : CochainComplex C ℤ) (hM : M.Acyclic)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The literal successor map of the coherent native complex diagram. -/
def acyclicStageSuccMap (j : J) :
    (acyclicStages hG M hM j : CochainComplex C ℤ) ⟶
      (acyclicStages hG M hM (Order.succ j) : CochainComplex C ℤ) :=
  Subobject.ofLE _ _ (acyclicStages_monotone hG M hM (Order.le_succ j))

lemma acyclicStageSuccMap_eq (j : J) : acyclicStageSuccMap hG M hM j =
    (acyclicComplexStages hG M hM).map (homOfLE (Order.le_succ j)) := rfl

/-- Each successor is either already stationary or has its actual cokernel
isomorphic to a member of the single final shift-closed test family. -/
lemma acyclicStageSuccMap_quotient (j : J) (hj : ¬ IsMax j) :
    IsIso (acyclicStageSuccMap hG M hM j) ∨
      ∃ i : smallAcyclicTestIndex hG,
        Nonempty (cokernel (acyclicStageSuccMap hG M hM j) ≅ smallAcyclicTests hG i) := by
  classical
  by_cases htop : acyclicStages hG M hM j = ⊤
  · left
    have heq : acyclicStages hG M hM j = acyclicStages hG M hM (Order.succ j) := by
      rw [acyclicStages_succ hG M hM j hj, htop, acyclicGrowth_top]
    exact (Subobject.isoOfEq _ _ heq).isIso_hom
  · right
    obtain ⟨i, ⟨e⟩⟩ := acyclicGrowth_quotient hG M hM _
      (acyclicStages_acyclic hG M hM j) htop
    let eB := Subobject.isoOfEq _ _ (acyclicStages_succ hG M hM j hj)
    refine ⟨i, ⟨(cokernel.mapIso (acyclicStageSuccMap hG M hM j)
      (Subobject.ofLE _ _ (le_acyclicGrowth hG M hM (acyclicStages hG M hM j)))
      (Iso.refl _) eB ?_) ≪≫ e⟩⟩
    apply (cancel_mono (acyclicGrowth hG M hM (acyclicStages hG M hM j)).arrow).1
    simp only [acyclicStageSuccMap, eB, Subobject.isoOfEq, Category.assoc,
      Subobject.ofLE_arrow, Iso.refl_hom, Category.id_comp]

end CochainComplex
