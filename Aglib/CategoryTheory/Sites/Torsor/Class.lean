/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Hom
public import Aglib.CategoryTheory.Sites.Torsor.Augmentation

/-! # The original torsor class map and its coefficient naturality

The map is the class of the actual augmentation pushout, descended through the
existing equivariant-isomorphism quotient. No classification premise is used.
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
variable {L M : Sheaf J AddCommGrpCat.{w}}

variable {q : L ⟶ M} {P : Torsor L} {Q : Torsor M}

/-- The free-abelian presheaf morphism induced by a torsor morphism. -/
def torsorFreePresheafMap (r : Torsor.Hom q P Q) : torsorFreePresheaf P ⟶ torsorFreePresheaf Q :=
  Functor.whiskerRight r.map.hom AddCommGrpCat.free

/-- Torsor morphisms commute with the actual augmentation. -/
theorem torsorFreePresheafMap_augmentation (r : Torsor.Hom q P Q) :
    torsorFreePresheafMap r ≫ torsorAugmentationPresheaf Q = torsorAugmentationPresheaf P := by
  ext U x
  change FreeAbelianGroup.lift (fun _ => (1 : ULift.{w} ℤ))
      (FreeAbelianGroup.map (r.map.hom.app U) x) =
    FreeAbelianGroup.lift (fun _ => (1 : ULift.{w} ℤ)) x
  exact (FreeAbelianGroup.lift_comp _ (fun _ => (1 : ULift.{w} ℤ)) x).symm

/-- The induced map on actual augmentation kernels is the universal kernel lift. -/
def torsorKernelPresheafMap (r : Torsor.Hom q P Q) :
    torsorKernelPresheaf P ⟶ torsorKernelPresheaf Q :=
  (KernelFork.IsLimit.lift' (torsorKernelIsLimit Q) (torsorKernelInclusion P ≫
    torsorFreePresheafMap r)
    (by rw [Category.assoc, torsorFreePresheafMap_augmentation,
      torsorKernelInclusion_augmentation])).1

@[reassoc] theorem torsorKernelPresheafMap_inclusion (r : Torsor.Hom q P Q) :
    torsorKernelPresheafMap r ≫ torsorKernelInclusion Q =
      torsorKernelInclusion P ≫ torsorFreePresheafMap r :=
  (KernelFork.IsLimit.lift' (torsorKernelIsLimit Q) (torsorKernelInclusion P ≫
    torsorFreePresheafMap r)
    (by rw [Category.assoc, torsorFreePresheafMap_augmentation,
      torsorKernelInclusion_augmentation])).2

/-- Explicit restriction/coefficient formula for the universal kernel map. -/
theorem torsorKernelPresheafMap_apply (r : Torsor.Hom q P Q) (U : Cᵒᵖ)
    (x : AddAction.TorsorAugmentation.AugmentationKernel (P.carrier.obj.obj U)) :
    (torsorKernelPresheafMap r).app U x =
      AddAction.TorsorAugmentation.kernelMap (r.map.hom.app U) x := by
  apply Subtype.ext
  exact congrArg (fun k : torsorKernelPresheaf P ⟶ torsorFreePresheaf Q => k.app U x)
    (torsorKernelPresheafMap_inclusion r)

/-- Naturality of the canonical torsor-difference morphism before sheafification. -/
theorem torsorKernelDifference_naturality (r : Torsor.Hom q P Q) :
    torsorKernelPresheafMap r ≫ torsorKernelDifference Q =
      torsorKernelDifference P ≫ q.hom := by
  ext U x
  let := P.sectionAction U
  let := Q.sectionAction U
  change AddAction.TorsorAugmentation.kernelDifference (Q.unique_transport U)
      ((torsorKernelPresheafMap r).app U x) =
    q.hom.app U (AddAction.TorsorAugmentation.kernelDifference (P.unique_transport U) x)
  rw [torsorKernelPresheafMap_apply]
  exact AddAction.TorsorAugmentation.kernelDifference_naturality (P.unique_transport U)
    (Q.unique_transport U) (q.hom.app U).hom (r.map.hom.app U) (r.equivariant U) x

variable [HasSheafify J AddCommGrpCat.{w}]

/-- The map on sheafified augmentation kernels. -/
def torsorKernelSheafMap (r : Torsor.Hom q P Q) : torsorKernelSheaf P ⟶ torsorKernelSheaf Q :=
  (presheafToSheaf J AddCommGrpCat.{w}).map
    (torsorKernelPresheafMap r)

/-- The map on free abelian sheaves obtained by sheafifying the map induced by the torsor
morphism. -/
def torsorFreeSheafMap (r : Torsor.Hom q P Q) : torsorFreeSheaf P ⟶ torsorFreeSheaf Q :=
  (presheafToSheaf J AddCommGrpCat.{w}).map
    (torsorFreePresheafMap r)

/-- Morphism of the actual augmentation short exact sequences. -/
def torsorAugmentationComplexMap (r : Torsor.Hom q P Q) :
    torsorAugmentationComplex P ⟶ torsorAugmentationComplex Q where
  τ₁ := torsorKernelSheafMap r
  τ₂ := torsorFreeSheafMap r
  τ₃ := 𝟙 _
  comm₁₂ := by
    change (presheafToSheaf J AddCommGrpCat.{w}).map _ ≫
      (presheafToSheaf J AddCommGrpCat.{w}).map _ = _
    rw [← Functor.map_comp, torsorKernelPresheafMap_inclusion, Functor.map_comp]
    rfl
  comm₂₃ := by
    change (presheafToSheaf J AddCommGrpCat.{w}).map _ ≫
      (presheafToSheaf J AddCommGrpCat.{w}).map _ = _
    rw [← Functor.map_comp, torsorFreePresheafMap_augmentation]
    exact (Category.comp_id _).symm

/-- The canonical difference map commutes with sheafification and coefficient maps. -/
theorem torsorDifferenceSheafMap_naturality (r : Torsor.Hom q P Q) :
    torsorKernelSheafMap r ≫ torsorDifferenceSheafMap Q = torsorDifferenceSheafMap P ≫ q := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{w}
  apply (adj.homEquiv (torsorKernelPresheaf P) M).injective
  change adj.homEquiv _ _
      ((presheafToSheaf J AddCommGrpCat.{w}).map
        (torsorKernelPresheafMap r) ≫ (adj.homEquiv _ _).symm (torsorKernelDifference Q)) =
    adj.homEquiv _ _ ((adj.homEquiv _ _).symm (torsorKernelDifference P) ≫ q)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact torsorKernelDifference_naturality r


variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

section ExtClass
variable [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- Naturality of the constructed torsor class for every actual equivariant
sheaf map with the specified coefficient map. -/
theorem torsorExtClass_naturality (r : Torsor.Hom q P Q) :
    H.map q 1 (torsorExtClass P) = torsorExtClass Q := by
  have h := ShortComplex.ShortExact.extClass_naturality
    (torsorAugmentation_shortExact P) (torsorAugmentation_shortExact Q)
    (torsorAugmentationComplexMap r)
  change (torsorAugmentation_shortExact P).extClass.comp
      (Abelian.Ext.mk₀ (torsorKernelSheafMap r)) (add_zero 1) =
    (Abelian.Ext.mk₀ (𝟙 _)).comp (torsorAugmentation_shortExact Q).extClass (zero_add 1) at h
  rw [Abelian.Ext.mk₀_id_comp] at h
  rw [torsorExtClass_eq P, torsorExtClass_eq Q]
  change ((torsorAugmentation_shortExact P).extClass.comp
    (Abelian.Ext.mk₀ (torsorDifferenceSheafMap P)) (add_zero 1)).comp
      (Abelian.Ext.mk₀ q) (add_zero 1) = _
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    ← torsorDifferenceSheafMap_naturality r, ← Abelian.Ext.mk₀_comp_mk₀,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero, h]

/-- Equivariant sheaf isomorphisms preserve the canonical Ext class. -/
theorem torsorExtClass_iso {Q : Torsor L} (e : Torsor.Iso P Q) : torsorExtClass P =
  torsorExtClass Q := by
  have h := torsorExtClass_naturality
    (q := 𝟙 L) (P := P) (Q := Q) (⟨e.carrierIso.hom, e.equivariant⟩ : Torsor.Hom (𝟙 L) P Q)
  simpa only [H.map_id_apply] using h

/-- Descent of the canonical map to the actual sheaf-torsor isomorphism classes. -/
def torsorClassToH1 (L : Sheaf J AddCommGrpCat.{w}) : TorsorClass L → H L 1 :=
  _root_.Quotient.lift torsorExtClass (fun _ _ ⟨e⟩ => torsorExtClass_iso e)

@[simp] theorem torsorClassToH1_mk (P : Torsor L) :
    torsorClassToH1 L (_root_.Quotient.mk (Torsor.isomorphicSetoid L) P) = torsorExtClass P := rfl

end ExtClass
end CategoryTheory.Sheaf
