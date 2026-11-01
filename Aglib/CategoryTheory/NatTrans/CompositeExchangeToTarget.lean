/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.NatTrans.CompositeExchange
public import Aglib.CategoryTheory.NatTrans.OverComparisonEquation

/-! # Pasting actual exchanges preserves an original comparison to the structural image -/
@[expose] public noncomputable section
namespace CategoryTheory
open CategoryTheory.Functor
variable {A B C A' B' C' : Type*}
  [Category* A] [Category* B] [Category* C]
  [Category* A'] [Category* B'] [Category* C']
  {J S : A ⥤ B} {R : B ⥤ C} {F : A ⥤ C}
  {J' S' : A' ⥤ B'} {R' : B' ⥤ C'} {F' : A' ⥤ C'}
  {G : C ⥤ C'} {H : B ⥤ B'} {G' : A ⥤ A'}

/-- The complete square uses the specified compactified and structural exchanges. -/
def CompositeExchangeToTargetEquation (b : J ⟶ S) (b' : J' ⟶ S')
    (τ : S ⋙ R ≅ F) (τ' : S' ⋙ R' ≅ F')
    (βR : R ⋙ G ⟶ H ⋙ R') (e : J ⋙ H ≅ G' ⋙ J')
    (βF : F ⋙ G ⟶ G' ⋙ F') : Prop :=
  compositeExchange βR e ≫ whiskerLeft G' (whiskerRight b' R' ≫ τ'.hom) =
    whiskerRight (whiskerRight b R ≫ τ.hom) G ≫ βF

/-- Original open compatibility and structural-image pasting imply the whole raw square. -/
theorem compositeExchange_toTarget (b : J ⟶ S) (b' : J' ⟶ S')
    (τ : S ⋙ R ≅ F) (τ' : S' ⋙ R' ≅ F')
    (βR : R ⋙ G ⟶ H ⋙ R') (e : J ⋙ H ≅ G' ⋙ J')
    (βS : S ⋙ H ⟶ G' ⋙ S') (βF : F ⋙ G ⟶ G' ⋙ F')
    (hb : e.hom ≫ whiskerLeft G' b' = whiskerRight b H ≫ βS)
    (hτ : OverComparisonBaseChangeEquation τ τ' βF βR βS) :
    CompositeExchangeToTargetEquation b b' τ τ' βR e βF := by
  ext K
  have hK := congrArg (fun z => z.app K) hb
  change e.hom.app K ≫ b'.app (G'.obj K) = H.map (b.app K) ≫ βS.app K at hK
  have hT := congrArg (fun z => z ≫ τ'.hom.app (G'.obj K)) (hτ K)
  simp only [Category.assoc, Iso.inv_hom_id_app] at hT
  have hT' : G.map (τ.hom.app K) ≫ βF.app K =
      βR.app (S.obj K) ≫ R'.map (βS.app K) ≫ τ'.hom.app (G'.obj K) :=
    (Category.comp_id _).symm.trans ((Category.assoc _ _ _).trans hT)
  have hN : G.map (R.map (b.app K)) ≫ βR.app (S.obj K) =
      βR.app (J.obj K) ≫ R'.map (H.map (b.app K)) := βR.naturality (b.app K)
  change (compositeExchange βR e).app K ≫
      (R'.map (b'.app (G'.obj K)) ≫ τ'.hom.app (G'.obj K)) =
    G.map (R.map (b.app K) ≫ τ.hom.app K) ≫ βF.app K
  rw [compositeExchange_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R'.map_comp_assoc, hK, R'.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (βR.app (J.obj K)), ← hN, Category.assoc]
  rw [← hT']
end CategoryTheory
