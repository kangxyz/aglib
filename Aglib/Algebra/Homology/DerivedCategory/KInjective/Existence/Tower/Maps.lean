/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Tower.Iteration

/-! # Monicity of the actual tower transitions and cocone legs -/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {ι : Type w} (A : ι → CochainComplex C ℤ)
  (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The original unit together with its actual tower is a transfinite composition
of monomorphisms, using the already constructed successor maps. -/
def replacementMonoComposition :
    MorphismProperty.TransfiniteCompositionOfShape
      (MorphismProperty.monomorphisms (CochainComplex C ℤ ⥤ CochainComplex C ℤ))
      J (replacementIterationUnit A J) :=
  ((replacementSuccStruct A).transfiniteCompositionOfShapeιIteration J).ofLE
    (replacementSuccStruct_prop_le_monomorphisms A)

instance replacementTower_map_mono {i j : J} (f : i ⟶ j) :
    Mono ((replacementTower A J).map f) := by
  have : MorphismProperty.IsStableUnderTransfiniteComposition.{w}
      (MorphismProperty.monomorphisms (CochainComplex C ℤ ⥤ CochainComplex C ℤ)) := {}
  exact (replacementMonoComposition A J).mem_map f

instance replacementTowerAt_map_mono (K : CochainComplex C ℤ) {i j : J} (f : i ⟶ j) :
    Mono ((replacementTowerAt A J K).map f) :=
  inferInstanceAs (Mono (((replacementTower A J).map f).app K))

instance replacementTower_incl_mono (j : J) :
    Mono (((replacementSuccStruct A).iterationCocone J).ι.app j) := by
  have : MorphismProperty.IsStableUnderTransfiniteComposition.{w}
      (MorphismProperty.monomorphisms (CochainComplex C ℤ ⥤ CochainComplex C ℤ)) := {}
  exact (replacementMonoComposition A J).mem_incl_app j

end CochainComplex
