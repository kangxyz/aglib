/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Tower.Maps

/-! # Original successor properties inside the actual transfinite tower -/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {ι : Type w} (A : ι → CochainComplex C ℤ)
  (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  (K : CochainComplex C ℤ)

/-- The original evaluated iteration cocone. -/
abbrev replacementTowerAtCocone : Cocone (replacementTowerAt A J K) :=
  ((evaluation (CochainComplex C ℤ) (CochainComplex C ℤ)).obj K).mapCocone
    ((replacementSuccStruct A).iterationCocone J)

/-- The native successor identification evaluated at the original input. -/
def replacementTowerSuccessorIso (j : J) (hj : ¬ IsMax j) :
    (replacementTowerAt A J K).obj (Order.succ j) ≅
      (replacementStepFunctor A).obj ((replacementTowerAt A J K).obj j) :=
  ((replacementSuccStruct A).iterationFunctorObjSuccIso j hj).app K

lemma replacementTowerAt_map_succ (j : J) (hj : ¬ IsMax j) :
    (replacementTowerAt A J K).map (homOfLE (Order.le_succ j)) =
      (replacementStepUnit A).app ((replacementTowerAt A J K).obj j) ≫
        (replacementTowerSuccessorIso A J K j hj).inv :=
  congrArg (fun f => f.app K) (replacementTower_map_succ A J j hj)

/-- Every original stage test map is killed by the actual next transition. -/
def replacementTowerStageHomotopy (j : J) (hj : ¬ IsMax j) (i : ι)
    (f : A i ⟶ (replacementTowerAt A J K).obj j) :
    Homotopy (f ≫ (replacementTowerAt A J K).map (homOfLE (Order.le_succ j))) 0 := by
  rw [replacementTowerAt_map_succ A J K j hj]
  simpa only [Category.assoc, zero_comp] using
    (replacementStepHomotopy A _ i f).compRight (replacementTowerSuccessorIso A J K j hj).inv

set_option backward.isDefEq.respectTransparency false in
/-- Each original cocone component factors through an actual injective object,
using the next transition rather than assuming injectivity of the final stage. -/
lemma replacementTowerCocone_injectiveFactor (j : J) (hj : ¬ IsMax j) (n : ℤ) :
    ∃ (E : C) (_ : Injective E) (a : ((replacementTowerAt A J K).obj j).X n ⟶ E)
      (b : E ⟶ ((replacementIteration A J).obj K).X n),
      ((replacementTowerAtCocone A J K).ι.app j).f n = a ≫ b := by
  obtain ⟨E, hE, a, b, _hb, hab⟩ :=
    replacementStepUnit_injectiveFactor A ((replacementTowerAt A J K).obj j) n
  refine ⟨E, hE, a, b ≫ (replacementTowerSuccessorIso A J K j hj).inv.f n ≫
    ((replacementTowerAtCocone A J K).ι.app (Order.succ j)).f n, ?_⟩
  have h := congrArg (fun f => f.f n)
    ((replacementTowerAtCocone A J K).w (homOfLE (Order.le_succ j)))
  rw [replacementTowerAt_map_succ A J K j hj] at h
  simp only [HomologicalComplex.comp_f] at h
  rw [hab] at h
  simpa only [Functor.const, Category.assoc] using h.symm

end CochainComplex
