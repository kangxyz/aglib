/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Class

/-! # Coefficient isomorphisms on the original torsor carrier

The carrier is literally unchanged. The inverse coefficient morphism defines
the action, and both coefficient-relative maps are the identity on that carrier.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory.Sheaf

universe u v w e
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {L M : Sheaf J AddCommGrpCat.{w}}

/-- Change coefficients through an actual isomorphism on the same carrier. -/
def Torsor.ofCoefficientIso (P : Torsor L) (e : L ≅ M) : Torsor M where
  carrier := P.carrier
  action U a t := P.action U (e.inv.hom.app U a) t
  zero_action U t := by rw [map_zero]; exact P.zero_action U t
  add_action U a b t := by rw [map_add]; exact P.add_action U _ _ t
  naturality {U V} f a t := by
    rw [P.naturality]
    congr 1
    exact (ConcreteCategory.congr_hom (e.inv.hom.naturality f) a).symm
  unique_transport U x y := by
    obtain ⟨a, ha, hu⟩ := P.unique_transport U x y
    have hleft (b : L.obj.obj U) : e.inv.hom.app U (e.hom.hom.app U b) = b :=
      congrArg (fun q : L ⟶ L => q.hom.app U b) e.hom_inv_id
    have hright (b : M.obj.obj U) : e.hom.hom.app U (e.inv.hom.app U b) = b :=
      congrArg (fun q : M ⟶ M => q.hom.app U b) e.inv_hom_id
    refine ⟨e.hom.hom.app U a, ?_, ?_⟩
    · change P.action U (e.inv.hom.app U (e.hom.hom.app U a)) x = y
      rw [hleft]
      exact ha
    · intro b hb
      exact (hright b).symm.trans (congrArg (e.hom.hom.app U) (hu _ hb))
  locally_nonempty := P.locally_nonempty

/-- The forward coefficient-relative map is the original identity carrier map. -/
def Torsor.coefficientIsoHom (P : Torsor L) (e : L ≅ M) :
    Torsor.Hom e.hom P (P.ofCoefficientIso e) where
  map := 𝟙 P.carrier
  equivariant U a t := by
    change P.action U a t = P.action U (e.inv.hom.app U (e.hom.hom.app U a)) t
    rw [show e.inv.hom.app U (e.hom.hom.app U a) = a from
      congrArg (fun q : L ⟶ L => q.hom.app U a) e.hom_inv_id]

/-- The reverse coefficient-relative map is the same identity carrier map. -/
def Torsor.coefficientIsoInvHom (P : Torsor L) (e : L ≅ M) :
    Torsor.Hom e.inv (P.ofCoefficientIso e) P where
  map := 𝟙 P.carrier
  equivariant _ _ _ := rfl

variable [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- The canonical extension class commutes with the literal coefficient transport. -/
theorem torsorExtClass_ofCoefficientIso (P : Torsor L) (e : L ≅ M) :
    H.map e.hom 1 (torsorExtClass P) = torsorExtClass (P.ofCoefficientIso e) :=
  torsorExtClass_naturality (P.coefficientIsoHom e)

end CategoryTheory.Sheaf
