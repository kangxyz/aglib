/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Transport of prescribed isomorphism lifting through a functor square

A fully faithful source comparison and a faithful target comparison
transport an actual isomorphism lift, preserving the original forward map.
The square is the given natural isomorphism of the original functors.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']

/-- Transport a prescribed isomorphism lift through the actual functor square. -/
theorem exists_iso_lift_of_square (F : C ⥤ D) (F' : C' ⥤ D')
    (G : C ⥤ C') (H : D ⥤ D') (hG : G.FullyFaithful) [H.Faithful]
    (t : F ⋙ H ≅ G ⋙ F') (X Y : C) (e : F.obj X ≅ F.obj Y)
    (hlift : ∀ e' : F'.obj (G.obj X) ≅ F'.obj (G.obj Y),
      ∃ d : G.obj X ≅ G.obj Y, F'.map d.hom = e'.hom) :
    ∃ d : X ≅ Y, F.map d.hom = e.hom := by
  let e' := (t.app X).symm ≪≫ H.mapIso e ≪≫ t.app Y
  obtain ⟨d', hd'⟩ := hlift e'
  let d := hG.preimageIso d'
  refine ⟨d, H.map_injective ?_⟩
  have hd : G.map d.hom = d'.hom := hG.map_preimage d'.hom
  have ht := (NatIso.naturality_2 t d.hom).symm
  change H.map (F.map d.hom) =
    (t.app X).hom ≫ F'.map (G.map d.hom) ≫ (t.app Y).inv at ht
  rw [hd, hd'] at ht
  simpa only [e', Iso.trans_hom, Iso.symm_hom, mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using ht

end CategoryTheory.Functor
