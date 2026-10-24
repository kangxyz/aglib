/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Tower.Successor
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Monomorphisms
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# Native transfinite iteration of the actual replacement successor

The construction uses `SuccStruct.ofNatTrans` in the native endofunctor category.
It is generic transfinite recursion, not a new model-category replacement route.
The original natural unit and pointwise colimit cocones are retained. A final
regular stage with the required injectivity/detection properties remains a
separate theorem, not an assumption hidden in this construction.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {ι : Type w} (A : ι → CochainComplex C ℤ)

/-- The native successor structure on actual endofunctors. -/
abbrev replacementSuccStruct : SuccStruct (CochainComplex C ℤ ⥤ CochainComplex C ℤ) :=
  SuccStruct.ofNatTrans (replacementStepUnit A)

variable (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The actual transfinite diagram of endofunctors. -/
abbrev replacementTower : J ⥤ (CochainComplex C ℤ ⥤ CochainComplex C ℤ) :=
  (replacementSuccStruct A).iterationFunctor J

/-- The actual colimit endofunctor of the transfinite tower. -/
abbrev replacementIteration : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  (replacementSuccStruct A).iteration J

/-- The original natural inclusion from the identity to the tower colimit. -/
abbrev replacementIterationUnit : 𝟭 (CochainComplex C ℤ) ⟶ replacementIteration A J :=
  (replacementSuccStruct A).ιIteration J

/-- The original tower evaluated at one complex, without changing its carrier. -/
abbrev replacementTowerAt (K : CochainComplex C ℤ) : J ⥤ CochainComplex C ℤ :=
  replacementTower A J ⋙ (evaluation (CochainComplex C ℤ) (CochainComplex C ℤ)).obj K

/-- Pointwise evaluation of the actual endofunctor colimit is a genuine colimit. -/
def replacementTowerAtIsColimit (K : CochainComplex C ℤ) :
    IsColimit (((evaluation (CochainComplex C ℤ) (CochainComplex C ℤ)).obj K).mapCocone
      ((replacementSuccStruct A).iterationCocone J)) :=
  isColimitOfPreserves _ ((replacementSuccStruct A).isColimitIterationCocone J)

/-- The original successor structure consists of monomorphisms. -/
lemma replacementSuccStruct_prop_le_monomorphisms :
    (replacementSuccStruct A).prop ≤
      MorphismProperty.monomorphisms (CochainComplex C ℤ ⥤ CochainComplex C ℤ) := by
  rw [SuccStruct.prop, MorphismProperty.ofHoms_le_iff]
  intro G
  change Mono (Functor.whiskerLeft G (replacementStepUnit A))
  have (K : CochainComplex C ℤ) :
      Mono ((Functor.whiskerLeft G (replacementStepUnit A)).app K) :=
    inferInstanceAs (Mono ((replacementStepUnit A).app (G.obj K)))
  exact NatTrans.mono_of_mono_app _

/-- The original transfinite natural unit is monic, by native stability of
monomorphisms under transfinite composition in Grothendieck categories. -/
instance replacementIterationUnit_mono : Mono (replacementIterationUnit A J) := by
  have h := ((replacementSuccStruct A).transfiniteCompositionOfShapeιIteration J).ofLE
    (replacementSuccStruct_prop_le_monomorphisms A)
  exact (MorphismProperty.monomorphisms _).transfiniteCompositionsOfShape_le J _ h.mem

instance replacementIterationUnit_app_mono (K : CochainComplex C ℤ) :
    Mono ((replacementIterationUnit A J).app K) := inferInstance

/-- The tower is continuous at all limit stages, by the native iteration proof. -/
instance replacementTower_continuous : (replacementTower A J).IsWellOrderContinuous :=
  inferInstanceAs ((replacementSuccStruct A).iterationFunctor J).IsWellOrderContinuous

/-- Successor transitions retain the original combined unit, up to the native
successor-stage identification. -/
lemma replacementTower_map_succ (j : J) (hj : ¬ IsMax j) :
    (replacementTower A J).map (homOfLE (Order.le_succ j)) =
      Functor.whiskerLeft ((replacementTower A J).obj j) (replacementStepUnit A) ≫
        ((replacementSuccStruct A).iterationFunctorObjSuccIso j hj).inv :=
  (replacementSuccStruct A).iterationFunctor_map_succ j hj

end CochainComplex
