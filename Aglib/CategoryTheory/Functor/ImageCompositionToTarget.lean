/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Whiskering

/-! # The original image-composition map preserves the canonical comparison -/
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

/-- The literal raw-tower equation, retaining the supplied maps and all structural paths. -/
def ImageCompositionToTargetEquation : Prop :=
  ∀ K, Q.map (σ.app (J.obj K)) ≫ Q.map (R.map (c.hom.app K)) ≫
      d.hom.app (V.obj K) ≫ U.map (bV.app K) ≫ τV.hom.app K =
    Q.map (bI.app (P.obj (J.obj K))) ≫ τI.hom.app (P.obj (J.obj K)) ≫
      G.map (P.map (bJ.app K) ≫ τF.hom.app K) ≫ τFG.hom.app K

/-- The original open-composition square, mixed-mate square, and structural triangles
paste to the actual raw-tower square. No invertibility of any b is assumed. -/
theorem imageComposition_toTarget
    (hOpen : ∀ K, c.hom.app K ≫ bV.app K =
      L.map (bJ.app K) ≫ bL.app (S.obj K) ≫ e.hom.app K)
    (hMixed : ∀ M₀, σ.app M₀ ≫ R.map (bL.app M₀) ≫ γ.hom.app M₀ = bI.app (P.obj M₀))
    (hSquare : ∀ M₀, d.hom.app (M.obj M₀) ≫ τL.hom.app M₀ =
      Q.map (γ.hom.app M₀) ≫ τI.hom.app (P.obj M₀) ≫ τP.hom.app M₀)
    (hLeft : ∀ K, τL.hom.app (S.obj K) ≫ τJ.hom.app K =
      U.map (e.hom.app K) ≫ τV.hom.app K)
    (hRight : ∀ K, τP.hom.app (S.obj K) ≫ τJ.hom.app K =
      G.map (τF.hom.app K) ≫ τFG.hom.app K) :
    ImageCompositionToTargetEquation bJ bI bV σ c d τV τI τF τFG := by
  intro K
  have hd' : Q.map (R.map (c.hom.app K)) ≫ d.hom.app (V.obj K) =
      d.hom.app (L.obj (J.obj K)) ≫ U.map (c.hom.app K) := d.hom.naturality (c.hom.app K)
  have hdL : Q.map (R.map (bL.app (J.obj K))) ≫ d.hom.app (M.obj (J.obj K)) =
      d.hom.app (L.obj (J.obj K)) ≫ U.map (bL.app (J.obj K)) :=
    d.hom.naturality (bL.app (J.obj K))
  have hL : U.map (M.map (bJ.app K)) ≫ τL.hom.app (S.obj K) =
      τL.hom.app (J.obj K) ≫ T.map (bJ.app K) := τL.hom.naturality (bJ.app K)
  have hP : G.map (P.map (bJ.app K)) ≫ τP.hom.app (S.obj K) =
      τP.hom.app (J.obj K) ≫ T.map (bJ.app K) := τP.hom.naturality (bJ.app K)
  rw [← Category.assoc (Q.map (R.map (c.hom.app K))), hd', Category.assoc,
    ← U.map_comp_assoc, hOpen]
  rw [← Category.assoc (L.map (bJ.app K)), bL.naturality]
  simp only [U.map_comp, Category.assoc]
  rw [← hLeft, ← Category.assoc (U.map (M.map (bJ.app K))), hL]
  simp only [Category.assoc]
  rw [← Category.assoc (d.hom.app (L.obj (J.obj K))), ← hdL, Category.assoc,
    ← Category.assoc (d.hom.app (M.obj (J.obj K))), hSquare]
  simp only [Category.assoc]
  rw [← Q.map_comp_assoc, ← Q.map_comp_assoc, Category.assoc, hMixed]
  rw [← Category.assoc (τP.hom.app (J.obj K)), ← hP]
  simp only [Category.assoc]
  rw [hRight, G.map_comp]
  simp only [Category.assoc]
end CategoryTheory
