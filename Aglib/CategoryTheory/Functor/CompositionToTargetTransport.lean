/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Functor.CompositionChoice
public import Aglib.CategoryTheory.NatTrans.TargetComparisonEquation

/-! # Descent of the same comparison through original composition model squares -/
@[expose] public section
namespace CategoryTheory
variable {A B C A₀ B₀ C₀ : Type*}
  [Category* A] [Category* B] [Category* C]
  [Category* A₀] [Category* B₀] [Category* C₀]
  (a : A₀ ⥤ A) (b : B₀ ⥤ B) (c : C₀ ⥤ C)
  {F Fm : A₀ ⥤ B₀} {G Gm : B₀ ⥤ C₀} {H Hm : A₀ ⥤ C₀}
  {R : A ⥤ B} {S : B ⥤ C} {T : A ⥤ C}

/-- Original compositor compatibility for a specified map into the ordinary functors. -/
def CompositionToTargetEquation (βF : F ⋙ b ⟶ a ⋙ R) (βG : G ⋙ c ⟶ b ⋙ S)
    (βH : H ⋙ c ⟶ a ⋙ T) (κ : F ⋙ G ≅ H) (ρ : R ⋙ S ≅ T) : Prop :=
  ∀ K, c.map (κ.hom.app K) ≫ βH.app K =
    βG.app (F.obj K) ≫ S.map (βF.app K) ≫ ρ.hom.app (a.obj K)

/-- Actual model comparisons preserving β and an actual compositor square descend the
raw compatibility to the chosen functors, without inferring it from invertibility. -/
theorem compositionToTarget_transport
    (βF : F ⋙ b ⟶ a ⋙ R) (βG : G ⋙ c ⟶ b ⋙ S) (βH : H ⋙ c ⟶ a ⋙ T)
    (μF : Fm ⋙ b ⟶ a ⋙ R) (μG : Gm ⋙ c ⟶ b ⋙ S) (μH : Hm ⋙ c ⟶ a ⋙ T)
    (κ : F ⋙ G ≅ H) (κm : Fm ⋙ Gm ≅ Hm) (ρ : R ⋙ S ≅ T)
    (eF : F ≅ Fm) (eG : G ≅ Gm) (eH : H ≅ Hm)
    (hF : TargetComparisonEquation (Functor.whiskerRight eF.hom b) μF βF)
    (hG : TargetComparisonEquation (Functor.whiskerRight eG.hom c) μG βG)
    (hH : TargetComparisonEquation (Functor.whiskerRight eH.hom c) μH βH)
    (hκ : compositionPairIso eF eG ≪≫ κm = κ ≪≫ eH)
    (hm : CompositionToTargetEquation a b c μF μG μH κm ρ) :
    CompositionToTargetEquation a b c βF βG βH κ ρ := by
  intro K
  have hFK : b.map (eF.hom.app K) ≫ μF.app K = βF.app K :=
    congrArg (fun z => z.app K) hF
  have hGK : c.map (eG.hom.app (Fm.obj K)) ≫ μG.app (Fm.obj K) = βG.app (Fm.obj K) :=
    congrArg (fun z => z.app (Fm.obj K)) hG
  have hHK : c.map (eH.hom.app K) ≫ μH.app K = βH.app K :=
    congrArg (fun z => z.app K) hH
  have hκK := congrArg (fun z => c.map (z.hom.app K)) hκ
  simp only [compositionPairIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, c.map_comp] at hκK
  have hN : c.map (G.map (eF.hom.app K)) ≫ βG.app (Fm.obj K) =
      βG.app (F.obj K) ≫ S.map (b.map (eF.hom.app K)) := βG.naturality (eF.hom.app K)
  rw [← hHK, ← Category.assoc, ← hκK]
  simp only [Category.assoc]
  rw [hm]
  rw [← Category.assoc (c.map (eG.hom.app (Fm.obj K))), hGK,
    ← Category.assoc (c.map (G.map (eF.hom.app K))), hN]
  simp only [Category.assoc]
  rw [← S.map_comp_assoc, hFK]
end CategoryTheory
