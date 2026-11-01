/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Functor.ImageCompositionToTarget
public import Aglib.CategoryTheory.Functor.ImageCompositionRefinement
public import Aglib.CategoryTheory.Adjunction.TripleCompositionInverse
public import Aglib.CategoryTheory.NatTrans.StructuralTriangleComponents

/-! # Whole original faces for the canonical image-composition square -/
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

/-- All structural substitutions and component extraction occur in abstract categories. -/
theorem imageComposition_toTarget_faces
    (d₀ : R ⋙ Q ≅ U) (τFG₀ : F ⋙ G ≅ H)
    (hd : d₀ = d) (hfg : τFG₀ = τFG)
    (hOpen : OpenCompositionToTargetEquation bV bJ bL c e)
    (hMixed : ∀ M₀, σ.app M₀ ≫ R.map (bL.app M₀) ≫ γ.hom.app M₀ =
      bI.app (P.obj M₀))
    (hSquare : ImageCompositionStructuralEquation d₀ γ τI τL τP)
    (hLeft : Functor.isoWhiskerLeft S τL ≪≫ τJ =
      (Functor.associator S M U).symm ≪≫ Functor.isoWhiskerRight e U ≪≫ τV)
    (hRight : Functor.isoWhiskerLeft S τP ≪≫ τJ =
      (Functor.associator S P G).symm ≪≫ Functor.isoWhiskerRight τF G ≪≫ τFG₀) :
    ImageCompositionToTargetEquation bJ bI bV σ c d τV τI τF τFG := by
  subst d₀
  subst τFG₀
  exact imageComposition_toTarget bJ bI bL bV σ c d γ e τV τL τJ τI τP τF τFG
    hOpen hMixed hSquare (structuralTriangle_components _ _ _ _ hLeft)
    (structuralTriangle_components _ _ _ _ hRight)
end CategoryTheory
