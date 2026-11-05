/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.Mates.ChartNormalization

/-! # Complete chart-isomorphism cancellation before native specialization -/
@[expose] public section
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory.SourceChartMates
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂}
  {P P' : C₀ ⥤ C₁} {Q Q' : D₀ ⥤ D₁}
  {F : C₁ ⥤ C₂} {G : D₁ ⥤ D₂}
  {A : C₀ ⥤ C₂} {B : D₀ ⥤ D₂}

/-- The whole original right square cancels both chart inverse-image boundaries. -/
theorem rightIso_normalize (i : P ≅ P') (j : Q ≅ Q')
    (δ : R₀ ⋙ P' ≅ Q' ⋙ R₁) (ε : R₁ ⋙ F ≅ G ⋙ R₂)
    (s : A ≅ P' ⋙ F) (t : B ≅ Q' ⋙ G) :
    (rightIso
      (isoWhiskerLeft R₀ i ≪≫ δ ≪≫ isoWhiskerRight j.symm R₁) ε
      (s ≪≫ isoWhiskerRight i.symm F) (t ≪≫ isoWhiskerRight j.symm G)).hom =
        (rightIso δ ε s t).hom := by
  apply NatTrans.ext
  funext K
  simp only [rightIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Functor.map_comp,
    Category.id_comp, Category.assoc]
  simpa only [Category.id_comp, Iso.app_hom, Iso.app_inv,
    Iso.symm_inv, Functor.map_comp, Category.assoc] using normalize_component F G R₁ R₂ ε.hom
    (i.app (R₀.obj K)) (j.app K) (s.hom.app (R₀.obj K)) (δ.hom.app K) (t.inv.app K)

end CategoryTheory.SourceChartMates
