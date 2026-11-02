/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Functor.ImageCompositionToTargetComponents
public import Aglib.CategoryTheory.Functor.ImageCompositionAssembly
public import Aglib.CategoryTheory.Functor.CompositionToTargetTransport

/-! # Whole raw-tower compatibility for the actual ambient composition map -/
@[expose] public noncomputable section
namespace CategoryTheory
variable {A B C D E Z : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* Z]
  {J S : A ⥤ B} {P : B ⥤ C} {I N : C ⥤ E} {L : B ⥤ D}
  {V W : A ⥤ D} {R : D ⥤ E} {Q : E ⥤ Z} {U : D ⥤ Z}
  {F : A ⥤ C} {G : C ⥤ Z} {H : A ⥤ Z}

/-- The whole original raw square consumes the actual assembled ambient map formula. -/
theorem imageCompositionToTarget_ambient
    (bJ : J ⟶ S) (bI : I ⟶ N) (bV : V ⟶ W)
    (σ : P ⋙ I ⟶ L ⋙ R) (c : J ⋙ L ≅ V) (d : R ⋙ Q ≅ U)
    (τV : W ⋙ U ≅ H) (τI : N ⋙ Q ≅ G) (τF : S ⋙ P ≅ F) (τFG : F ⋙ G ≅ H)
    (κ : (J ⋙ P) ⋙ (I ⋙ Q) ≅ V ⋙ U)
    (hκ : ImageCompositionFormula σ c d κ.hom)
    (h : ImageCompositionToTargetEquation bJ bI bV σ c d τV τI τF τFG) :
    CompositionToTargetEquation (𝟭 A) (𝟭 C) (𝟭 Z)
      (Functor.whiskerRight bJ P ≫ τF.hom)
      (Functor.whiskerRight bI Q ≫ τI.hom)
      (Functor.whiskerRight bV U ≫ τV.hom) κ τFG := by
  intro K
  change κ.hom.app K ≫ (U.map (bV.app K) ≫ τV.hom.app K) =
    (Q.map (bI.app (P.obj (J.obj K))) ≫ τI.hom.app (P.obj (J.obj K))) ≫
      G.map (P.map (bJ.app K) ≫ τF.hom.app K) ≫ τFG.hom.app K
  rw [hκ]
  exact imageCompositionToTarget_components bJ bI bV σ c d τV τI τF τFG h K
end CategoryTheory
