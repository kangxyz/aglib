/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Functor.ImageCompositionToTargetComponents
public import Aglib.CategoryTheory.Functor.ImageCompositionAssembly
public import Aglib.CategoryTheory.Functor.CompositionToTargetTransport
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Whole raw-tower compatibility restricts through the actual torsion lifts -/
@[expose] public noncomputable section
namespace CategoryTheory
variable {A B C D E Z : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* Z]
  {J S : A ⥤ B} {P : B ⥤ C} {I N : C ⥤ E} {L : B ⥤ D}
  {V W : A ⥤ D} {R : D ⥤ E} {Q : E ⥤ Z} {U : D ⥤ Z}
  {F : A ⥤ C} {G : C ⥤ Z} {H : A ⥤ Z}

/-- Restrict the whole original raw square using the whole actual compositor formula.
No concrete coefficient category or object-property carrier is expanded by a consumer. -/
theorem imageCompositionToTarget_restrict
    (bJ : J ⟶ S) (bI : I ⟶ N) (bV : V ⟶ W)
    (σ : P ⋙ I ⟶ L ⋙ R) (c : J ⋙ L ≅ V) (d : R ⋙ Q ≅ U)
    (τV : W ⋙ U ≅ H) (τI : N ⋙ Q ≅ G) (τF : S ⋙ P ≅ F) (τFG : F ⋙ G ≅ H)
    (PA : ObjectProperty A) (PC : ObjectProperty C) (PZ : ObjectProperty Z)
    (hF : ∀ K : PA.FullSubcategory, PC ((PA.ι ⋙ (J ⋙ P)).obj K))
    (hG : ∀ K : PC.FullSubcategory, PZ ((PC.ι ⋙ (I ⋙ Q)).obj K))
    (hH : ∀ K : PA.FullSubcategory, PZ ((PA.ι ⋙ (V ⋙ U)).obj K))
    (κ : PC.lift (PA.ι ⋙ (J ⋙ P)) hF ⋙ PZ.lift (PC.ι ⋙ (I ⋙ Q)) hG ≅
      PZ.lift (PA.ι ⋙ (V ⋙ U)) hH)
    (α : (PA.ι ⋙ J) ⋙ P ⋙ I ⋙ Q ⟶ (PA.ι ⋙ V) ⋙ U)
    (hκ : Functor.whiskerRight κ.hom PZ.ι = α)
    (hα : ImageCompositionFormula σ (Functor.isoWhiskerLeft PA.ι c) d α)
    (h : ImageCompositionToTargetEquation bJ bI bV σ c d τV τI τF τFG) :
    CompositionToTargetEquation
      (F := PC.lift (PA.ι ⋙ (J ⋙ P)) hF)
      (G := PZ.lift (PC.ι ⋙ (I ⋙ Q)) hG)
      (H := PZ.lift (PA.ι ⋙ (V ⋙ U)) hH)
      PA.ι PC.ι PZ.ι
      (Functor.whiskerLeft PA.ι (Functor.whiskerRight bJ P ≫ τF.hom))
      (Functor.whiskerLeft PC.ι (Functor.whiskerRight bI Q ≫ τI.hom))
      (Functor.whiskerLeft PA.ι (Functor.whiskerRight bV U ≫ τV.hom)) κ τFG := by
  intro K
  have hκK : PZ.ι.map (κ.hom.app K) = α.app K := congrArg (fun z => z.app K) hκ
  change PZ.ι.map (κ.hom.app K) ≫ (U.map (bV.app K.obj) ≫ τV.hom.app K.obj) =
    (Q.map (bI.app (P.obj (J.obj K.obj))) ≫ τI.hom.app (P.obj (J.obj K.obj))) ≫
      G.map (P.map (bJ.app K.obj) ≫ τF.hom.app K.obj) ≫ τFG.hom.app K.obj
  rw [hκK, hα]
  exact imageCompositionToTarget_components bJ bI bV σ c d τV τI τF τFG h K.obj
end CategoryTheory
