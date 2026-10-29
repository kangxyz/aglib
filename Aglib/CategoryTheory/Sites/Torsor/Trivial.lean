/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Classification

/-! # Global points and vanishing of the actual torsor Ext class

A genuine intrinsic global point extends the original positive kernel difference
map. The converse uses the proved classifier and the original torsor Iso relation.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w e
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {L : Sheaf J AddCommGrpCat.{w}}
variable (P : Torsor L) (s : Topos.GlobalPoint P.carrier)

private theorem globalPoint_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    P.carrier.obj.map f (s.hom.app U PUnit.unit) = s.hom.app V PUnit.unit :=
  (ConcreteCategory.congr_hom (s.hom.naturality f) PUnit.unit).symm

/-- A chosen global section extends the difference map to the free presheaf. -/
def torsorBasedDifferencePresheaf : torsorFreePresheaf P ⟶ L.obj where
  app U := by
    let := P.sectionAction U
    exact AddCommGrpCat.ofHom (AddAction.TorsorAugmentation.basedDifference
      (P.unique_transport U) (s.hom.app U PUnit.unit))
  naturality {U V} f := by
    let := P.sectionAction U
    let := P.sectionAction V
    ext x
    have h := AddAction.TorsorAugmentation.basedDifference_naturality
      (P.unique_transport U) (P.unique_transport V) (L.obj.map f).hom
      (P.carrier.obj.map f) (P.naturality f) (s.hom.app U PUnit.unit)
    rw [globalPoint_naturality P s] at h
    exact DFunLike.congr_fun h x

/-- The section-based extension restricts to the canonical kernel difference. -/
theorem torsorBasedDifferencePresheaf_kernel :
    torsorKernelInclusion P ≫ torsorBasedDifferencePresheaf P s = torsorKernelDifference P := by
  ext U x
  let := P.sectionAction U
  exact (AddAction.TorsorAugmentation.kernelDifference_eq_based (P.unique_transport U)
    (s.hom.app U PUnit.unit) x).symm

variable [HasSheafify J AddCommGrpCat.{w}]

/-- The induced map from the actual free abelian sheaf. -/
def torsorBasedDifferenceSheaf : torsorFreeSheaf P ⟶ L :=
  ((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv
    (torsorFreePresheaf P) L).symm (torsorBasedDifferencePresheaf P s)

/-- The canonical kernel difference extends to the free sheaf when a section exists. -/
theorem torsorBasedDifferenceSheaf_kernel :
    torsorKernelSheafInclusion P ≫ torsorBasedDifferenceSheaf P s = torsorDifferenceSheafMap P := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{w}
  apply (adj.homEquiv (torsorKernelPresheaf P) L).injective
  change adj.homEquiv _ _
      ((presheafToSheaf J AddCommGrpCat.{w}).map
        (torsorKernelInclusion P) ≫ (adj.homEquiv _ _).symm (torsorBasedDifferencePresheaf P s)) =
    adj.homEquiv _ _ ((adj.homEquiv _ _).symm (torsorKernelDifference P))
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact torsorBasedDifferencePresheaf_kernel P s

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

include s in
/-- A genuine global torsor section forces the canonical Ext class to vanish. -/
theorem torsorExtClass_eq_zero_of_globalPoint : torsorExtClass P = 0 := by
  rw [torsorExtClass_eq, ← torsorBasedDifferenceSheaf_kernel P s,
    ← Abelian.Ext.mk₀_comp_mk₀]
  exact (torsorAugmentation_shortExact P).extClass_comp_assoc
    (Abelian.Ext.mk₀ (torsorBasedDifferenceSheaf P s))

/-- The original regular translation torsor has zero canonical class. -/
@[simp] theorem torsorExtClass_trivial (L : Sheaf J AddCommGrpCat.{w}) :
    torsorExtClass (trivialTorsor L) = 0 := by
  obtain ⟨s⟩ := (trivialTorsor L).nonempty_globalPoints_iff_trivial.mpr
    ⟨Torsor.Iso.refl (trivialTorsor L)⟩
  exact torsorExtClass_eq_zero_of_globalPoint (trivialTorsor L) s

/-- Vanishing is equivalent to a genuine intrinsic global point, by the proved classifier. -/
theorem torsorExtClass_eq_zero_iff_globalPoint :
    torsorExtClass P = 0 ↔ Nonempty (Topos.GlobalPoint P.carrier) := by
  constructor
  · intro hp
    have hc : torsorClassToH1 L (_root_.Quotient.mk (Torsor.isomorphicSetoid L) P) =
        torsorClassToH1 L (_root_.Quotient.mk (Torsor.isomorphicSetoid L) (trivialTorsor L)) :=
      hp.trans (torsorExtClass_trivial L).symm
    have he := (torsorClassToH1_bijective L).injective hc
    obtain ⟨e⟩ := _root_.Quotient.exact he
    exact P.nonempty_globalPoints_iff_trivial.mpr ⟨e.symm⟩
  · rintro ⟨t⟩
    exact torsorExtClass_eq_zero_of_globalPoint P t

end CategoryTheory.Sheaf
