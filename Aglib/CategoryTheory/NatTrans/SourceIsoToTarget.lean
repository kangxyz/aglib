/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.NatTrans.ExchangeToTarget

/-! # Identity-base exchange and the same comparison under source transport -/
@[expose] public section
namespace CategoryTheory
open CategoryTheory.Functor
variable {A A' B : Type*} [Category* A] [Category* A'] [Category* B]
  {R F : A ⥤ B} {R' F' : A' ⥤ B} {H : A ⥤ A'} {I : B ⥤ B}

/-- Normalize an actual exchange only by its supplied base identity comparison. -/
def identityBaseExchange (d : I ≅ 𝟭 B) (γ : F ⋙ I ⟶ H ⋙ F') : F ⟶ H ⋙ F' :=
  (rightUnitor F).inv ≫ whiskerLeft F d.inv ≫ γ

/-- The original exchange square gives the source-transport square, retaining its map. -/
theorem sourceIso_toTarget (b : R ⟶ F) (b' : R' ⟶ F')
    (β : R ⋙ I ⟶ H ⋙ R') (γ : F ⋙ I ⟶ H ⋙ F')
    (d : I ≅ 𝟭 B) (s : R ≅ H ⋙ R')
    (hs : ∀ K, β.app K = d.hom.app (R.obj K) ≫ s.hom.app K)
    (h : ExchangeToTargetEquation b b' β γ) :
    TargetComparisonEquation s.hom (whiskerLeft H b')
      (b ≫ identityBaseExchange d γ) := by
  ext K
  have hK := congrArg (fun z => z.app K) h
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hK
  rw [hs K, Category.assoc] at hK
  apply (cancel_epi (d.hom.app (R.obj K))).1
  simp only [NatTrans.comp_app, whiskerLeft_app, identityBaseExchange,
    rightUnitor_inv_app, Category.id_comp]
  have hn : d.hom.app (R.obj K) ≫ b.app K =
      I.map (b.app K) ≫ d.hom.app (F.obj K) := (d.hom.naturality (b.app K)).symm
  rw [reassoc_of% hn]
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hK
end CategoryTheory
