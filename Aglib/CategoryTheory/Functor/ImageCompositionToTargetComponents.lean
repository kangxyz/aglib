/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Functor.ImageCompositionToTarget

/-! # Exact component grouping of the original image-composition comparison -/
@[expose] public section
namespace CategoryTheory
variable {A B C D E Z : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* Z]
  {J S : A ⥤ B} {P : B ⥤ C} {I N : C ⥤ E} {L M : B ⥤ D}
  {V W : A ⥤ D} {R : D ⥤ E} {Q : E ⥤ Z} {U : D ⥤ Z}
  {F : A ⥤ C} {G : C ⥤ Z} {H : A ⥤ Z} {T : B ⥤ Z}
  (bJ : J ⟶ S) (bI : I ⟶ N) (bL : L ⟶ M) (bV : V ⟶ W)
  (σ : P ⋙ I ⟶ L ⋙ R) (c : J ⋙ L ≅ V) (d : R ⋙ Q ≅ U)
  (γ : M ⋙ R ≅ P ⋙ N) (e : S ⋙ M ≅ W)
  (τV : W ⋙ U ≅ H) (τL : M ⋙ U ≅ T) (τJ : S ⋙ T ≅ H)
  (τI : N ⋙ Q ≅ G) (τP : P ⋙ G ≅ T) (τF : S ⋙ P ≅ F) (τFG : F ⋙ G ≅ H)

/-- Keep the original compositor and both model maps parenthesized at the abstract boundary. -/
theorem imageCompositionToTarget_components
    (h : ImageCompositionToTargetEquation bJ bI bV σ c d τV τI τF τFG) (K : A) :
    (Q.map (σ.app (J.obj K)) ≫ Q.map (R.map (c.hom.app K)) ≫ d.hom.app (V.obj K)) ≫
        (U.map (bV.app K) ≫ τV.hom.app K) =
      (Q.map (bI.app (P.obj (J.obj K))) ≫ τI.hom.app (P.obj (J.obj K))) ≫
        G.map (P.map (bJ.app K) ≫ τF.hom.app K) ≫ τFG.hom.app K := by
  simpa only [Category.assoc] using h K
end CategoryTheory
