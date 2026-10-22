/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Original locally directed inverse-image affine covers

Only the actual inverse-image affine opens and native `Spec.map` are used.
The local maps and their original coordinate equations are glued together;
no relative spectrum or category of affine algebras is introduced.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.Algebra

variable {X Y Z : Scheme.{u}}

/-- The original inverse images of all affine opens form an open cover. -/
def affineInverseImageCover (p : Y ⟶ X) : Y.OpenCover :=
  Y.openCoverOfIsOpenCover (fun U : X.affineOpens => p ⁻¹ᵁ U.val)
    (p.iSup_preimage_eq_top (iSup_affineOpens_eq_top X))

/-- The affine inverse-image cover uses the inclusion order of affine opens on the base. -/
instance instPreorderAffineInverseImageCover (p : Y ⟶ X) :
    Preorder (affineInverseImageCover p).I₀ :=
  inferInstanceAs (Preorder X.affineOpens)

/-- The inverse-image cover is locally directed by inclusions on the base. -/
instance instLocallyDirectedAffineInverseImageCover (p : Y ⟶ X) :
    (affineInverseImageCover p).LocallyDirected where
  trans {U V} i := Y.homOfLE (p.preimage_mono i.le)
  trans_id U := by apply Scheme.homOfLE_rfl
  trans_comp i j := (Scheme.homOfLE_homOfLE _ _ _).symm
  w i := Scheme.homOfLE_ι _ _
  directed {U V} x := by
    change (pullback (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι).carrier at x
    let y := pullback.fst (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι x
    have hxV : p y.val ∈ V.val := by
      have h := congrArg (fun f : pullback (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι ⟶ Y => f x)
        (pullback.condition (f := (p ⁻¹ᵁ U.val).ι) (g := (p ⁻¹ᵁ V.val).ι))
      change y.val = (pullback.snd (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι x).val at h
      rw [h]
      exact (pullback.snd (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι x).property
    obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show p y.val ∈ U.val ⊓ V.val from ⟨y.property, hxV⟩)
    refine ⟨⟨W, hW⟩, homOfLE (hWUV.trans inf_le_left),
      homOfLE (hWUV.trans inf_le_right), ⟨y.val, hxW⟩, ?_⟩
    apply (pullback.fst (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι ≫ (p ⁻¹ᵁ U.val).ι).isOpenEmbedding.injective
    change ((pullback.lift
      (Y.homOfLE (p.preimage_mono (hWUV.trans inf_le_left)))
      (Y.homOfLE (p.preimage_mono (hWUV.trans inf_le_right))) _ ≫
      pullback.fst (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι ≫ (p ⁻¹ᵁ U.val).ι)
        ⟨y.val, hxW⟩) = y.val
    rw [pullback.lift_fst_assoc, Scheme.homOfLE_ι]
    rfl
  property_trans i := inferInstance

@[simp] theorem affineInverseImageCover_trans (p : Y ⟶ X)
    {U V : X.affineOpens} (i : U ⟶ V) :
    (affineInverseImageCover p).trans i = Y.homOfLE (p.preimage_mono i.le) := rfl

/-- The original affine-open spectrum isomorphisms preserve restriction maps. -/
@[reassoc] theorem affineOpen_isoSpec_inv_restriction
    {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : V ⟶ U) :
    Spec.map (Y.presheaf.map i.op) ≫ hU.isoSpec.inv =
      hV.isoSpec.inv ≫ Y.homOfLE i.le := by
  apply (cancel_mono U.ι).mp
  simpa only [Category.assoc, Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι] using
    hU.map_fromSpec hV i.op

end AlgebraicGeometry.Scheme.Modules.Algebra
