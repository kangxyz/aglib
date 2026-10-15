/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Postcomposition and precomposition of a genuine natural unit

Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/OriginalUnitPostcomposition.lean`
at LOCAL Quillen `189a8e779f0c68b2dfc6f8195daebb3e684a5905`; generic unit definitions and
component equation only.
-/

@[expose] public section
noncomputable section
open CategoryTheory
namespace CategoryTheory.NatTrans

/-- Postcompose the unit `η : 𝟭 A ⟶ G` with `F`, giving components `F.map (η.app K)`. -/
def unitPostcompose {A : Type*} [Category A] (G F : A ⥤ A)
    (η : 𝟭 A ⟶ G) : F ⟶ G ⋙ F where
  app K := F.map (η.app K)
  naturality {K C} f := by
    change F.map f ≫ F.map (η.app C) = F.map (η.app K) ≫ F.map (G.map f)
    simp only [← Functor.map_comp]
    exact congrArg F.map (η.naturality f)

/-- The actual further postcomposition of this unit. -/
def unitTotalPostcompose {A : Type*} [Category A] (G F T : A ⥤ A)
    (η : 𝟭 A ⟶ G) : F ⋙ T ⟶ (G ⋙ F) ⋙ T :=
  Functor.whiskerRight (unitPostcompose G F η) T

/-- Its literal component uses the original unit in its original order. -/
lemma unitTotalPostcompose_app {A : Type*} [Category A]
    (G F T : A ⥤ A) (η : 𝟭 A ⟶ G) (K : A) :
    (unitTotalPostcompose G F T η).app K = T.map (F.map (η.app K)) := rfl


/-- Precompose the unit `η : 𝟭 A ⟶ T` with `F`, giving components `η.app (F.obj K)`. -/
def unitPrecompose {A : Type*} [Category A] (T F : A ⥤ A)
    (η : 𝟭 A ⟶ T) : F ⟶ F ⋙ T where
  app K := η.app (F.obj K)
  naturality {_K _C} f := η.naturality (F.map f)


end CategoryTheory.NatTrans
