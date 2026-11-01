/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Identity normalization of an exchange in independent target models -/

@[expose] public noncomputable section
open CategoryTheory.Functor
namespace CategoryTheory
variable {A B₀ B₁ A' : Type*}
  [Category* A] [Category* B₀] [Category* B₁] [Category* A']
  {F : A ⥤ B₀} {I : B₀ ⥤ B₀} {I' E : B₀ ⥤ B₁} {U : A ⥤ A'}
  {V₀ : A' ⥤ B₀} {V₁ : A' ⥤ B₁}

/-- A unit-normalized identity comparison and original target square identify the
independent-model exchange with independently transported source geometry. -/
theorem targetIdentityExchange
    (β₀ : F ⋙ I ≅ U ⋙ V₀) (β₁ : F ⋙ I' ≅ U ⋙ V₁)
    (s : I ⋙ E ≅ I') (t : V₀ ⋙ E ≅ V₁)
    (i : I ≅ 𝟭 B₀) (ι : I' ≅ E) (ψ : F ≅ U ⋙ V₀)
    (hi : ι = s.symm ≪≫ isoWhiskerRight i E ≪≫ leftUnitor E)
    (hβ : β₀ = isoWhiskerLeft F i ≪≫ rightUnitor F ≪≫ ψ)
    (hs : isoWhiskerRight β₀ E ≪≫ associator _ _ _ ≪≫ isoWhiskerLeft U t =
      associator _ _ _ ≪≫ isoWhiskerLeft F s ≪≫ β₁) :
    β₁ = isoWhiskerLeft F ι ≪≫
      (isoWhiskerRight ψ E ≪≫ associator _ _ _ ≪≫ isoWhiskerLeft U t) := by
  subst ι
  subst β₀
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hK := congrArg (fun z => z.hom.app K) hs
  apply (cancel_epi (s.hom.app (F.obj K))).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, rightUnitor_hom_app, leftUnitor_hom_app, Functor.map_comp,
    Functor.comp_obj, Functor.id_obj, Functor.map_id, Category.id_comp, Category.comp_id,
    Category.assoc,
    Iso.hom_inv_id_app_assoc] using hK.symm

end CategoryTheory
