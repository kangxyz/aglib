/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! # Restricting an original cartesian cover square

Only the chosen target open is required to be etale. The comparison is over
its actual inverse image, with the original source projection retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

/-- The literal restrictions of a cartesian cover square have the original
pullback comparison and its unchanged projection to the ambient source. -/
theorem exists_restrictSquare_comparison
    {X B N : Scheme.{u}} (f : N ⟶ X) (b : B ⟶ X)
    (Y : FiniteEtale B) (k : Y.obj.left ⟶ N)
    (H : IsPullback k Y.obj.hom f b) (V : X.Opens)
    [IsFinite (f ∣_ V)] [Etale (f ∣_ V)] :
    ∃ e : (baseChange (b ∣_ V)).obj (FiniteEtale.mk (f ∣_ V)) ≅
        (baseChange (b ⁻¹ᵁ V).ι).obj Y,
      e.inv.hom.left ≫ pullback.fst (f ∣_ V) (b ∣_ V) ≫ (f ⁻¹ᵁ V).ι =
        pullback.fst Y.obj.hom (b ⁻¹ᵁ V).ι ≫ k := by
  have hpre : k ⁻¹ᵁ (f ⁻¹ᵁ V) = Y.obj.hom ⁻¹ᵁ (b ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  let r := k.resLE (f ⁻¹ᵁ V) (Y.obj.hom ⁻¹ᵁ (b ⁻¹ᵁ V)) (le_of_eq hpre.symm)
  have HR : IsPullback r (Y.obj.hom ∣_ (b ⁻¹ᵁ V)) (f ∣_ V) (b ∣_ V) := by
    have h := Scheme.Hom.isPullback_resLE H
      (UT := b ⁻¹ᵁ V) (US := V) (UX := f ⁻¹ᵁ V) le_rfl le_rfl
      (UY := Y.obj.hom ⁻¹ᵁ (b ⁻¹ᵁ V)) (by rw [hpre, inf_idem])
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using h
  let HJ := (isPullback_morphismRestrict Y.obj.hom (b ⁻¹ᵁ V)).flip
  let eS := HR.isoPullback.symm ≪≫ HJ.isoPullback
  let e : (baseChange (b ∣_ V)).obj (FiniteEtale.mk (f ∣_ V)) ≅
      (baseChange (b ⁻¹ᵁ V).ι).obj Y :=
    ObjectProperty.isoMk _ (Over.isoMk eS (by
      change HR.isoPullback.inv ≫ HJ.isoPullback.hom ≫
        pullback.snd Y.obj.hom (b ⁻¹ᵁ V).ι = pullback.snd (f ∣_ V) (b ∣_ V)
      rw [HJ.isoPullback_hom_snd, HR.isoPullback_inv_snd]))
  refine ⟨e, ?_⟩
  change (HJ.isoPullback.inv ≫ HR.isoPullback.hom) ≫
    pullback.fst (f ∣_ V) (b ∣_ V) ≫ (f ⁻¹ᵁ V).ι = _
  rw [Category.assoc, HR.isoPullback_hom_fst_assoc]
  change HJ.isoPullback.inv ≫ r ≫ (f ⁻¹ᵁ V).ι = _
  rw [Scheme.Hom.resLE_comp_ι, HJ.isoPullback_inv_fst_assoc]

end AlgebraicGeometry.Scheme.FiniteEtale
