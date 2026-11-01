/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.CategoryTheory.NatTrans.CartesianSourceExchange

/-! # Identity source transport cancels in the original Cartesian exchange -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology

/-- Retain the given unit equation while solving for the original inverse compositor. -/
theorem cartesianSourceCompositor_of_unit
    {C : Type*} [Category* C] {X Y Z : C}
    (e : X ≅ Y) (a : X ≅ Z) (b : Z ≅ Y) (h : a ≪≫ b = e) :
    e.symm ≪≫ a = b.symm := by
  rw [← h, Iso.trans_symm, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- The original identity source comparison and compositor cancel, not just objectwise. -/
theorem cartesianSourceExchange_identity
    {A A' D D' : Type*} [Category* A] [Category* A'] [Category* D] [Category* D']
    {F : A ⥤ D} {H : A' ⥤ D'} {B : D ⥤ D'} {V : A ⥤ A'}
    (β : F ⋙ B ≅ V ⋙ H) {I : A' ⥤ A'} (d : I ≅ 𝟭 A') :
    cartesianSourceExchange β
        ((Functor.leftUnitor H).symm ≪≫ Functor.isoWhiskerRight d.symm H)
        ((Functor.rightUnitor V).symm ≪≫ Functor.isoWhiskerLeft V d.symm) = β := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  rw [cartesianSourceExchange_hom_app]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.id_comp]
  rw [← H.map_comp, Iso.inv_hom_id_app_assoc]
  exact (congrArg (fun z => β.hom.app K ≫ z) (H.map_id (V.obj K))).trans
    (Category.comp_id (β.hom.app K))

end AlgebraicGeometry.Scheme.EtaleCohomology
