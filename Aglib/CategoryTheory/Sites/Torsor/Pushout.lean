/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Class
public import Aglib.CategoryTheory.Sites.Torsor.ExtensionFiber

/-! # Actual coefficient pushouts and canonical extension recovery

The original generator maps to the original augmentation-one fibre in the
native pushout extension. Positive transport proves equivariance. The same
map recovers the original torsor from its canonical extension.
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
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {L M : Sheaf J AddCommGrpCat.{w}}
variable (P : Torsor L) (q : L ⟶ M)

/-- The actual coefficient pushout of the augmentation sequence. -/
def torsorCoefficientExtension : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  CategoryTheory.Abelian.ExtensionPushout.complex (torsorAugmentationComplex P)
    (torsorDifferenceSheafMap P ≫ q)

/-- This extension is short exact by the proved abelian pushout construction. -/
theorem torsorCoefficientExtension_shortExact : (torsorCoefficientExtension P q).ShortExact :=
  CategoryTheory.Abelian.ExtensionPushout.shortExact _ _ (torsorAugmentation_shortExact P)

/-- Coefficient pushout is constructed as a genuine sheaf torsor. -/
def torsorPushout : Torsor M :=
  extensionFiberTorsor (torsorCoefficientExtension P q) (constantIntegerOne J)
    (torsorCoefficientExtension_shortExact P q)

/-- The canonical generator section in the free abelian sheaf. -/
def torsorGenerator (U : Cᵒᵖ) (t : P.carrier.obj.obj U) : (torsorFreeSheaf P).obj.obj U :=
  (toSheafify J (torsorFreePresheaf P)).app U
    (FreeAbelianGroup.of t)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Generator sections respect restriction. -/
theorem torsorGenerator_naturality {U V : Cᵒᵖ} (f : U ⟶ V)
    (t : P.carrier.obj.obj U) :
    (torsorFreeSheaf P).obj.map f (torsorGenerator P U t) =
      torsorGenerator P V (P.carrier.obj.map f t) := by
  have h := ConcreteCategory.congr_hom
    ((toSheafify J (torsorFreePresheaf P)).naturality f)
    (FreeAbelianGroup.of t)
  change (toSheafify J (torsorFreePresheaf P)).app V
      (FreeAbelianGroup.map (P.carrier.obj.map f) (FreeAbelianGroup.of t)) = _ at h
  rw [FreeAbelianGroup.map_of_apply] at h
  exact h.symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Every original generator lies over the intrinsic integer-one global element. -/
theorem torsorGenerator_augmentation (U : Cᵒᵖ) (t : P.carrier.obj.obj U) :
    (torsorAugmentation P).hom.app U (torsorGenerator P U t) =
      (constantIntegerOne J).hom.app U PUnit.unit := by
  have h := congrArg (fun r => r.app U (FreeAbelianGroup.of t))
    (toSheafify_naturality J (torsorAugmentationPresheaf P))
  change (toSheafify J
      ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ)))).app U
        (FreeAbelianGroup.lift (fun _ : P.carrier.obj.obj U => (1 : ULift.{w} ℤ))
          (FreeAbelianGroup.of t)) = _ at h
  rw [FreeAbelianGroup.lift_apply_of] at h
  exact h.symm

/-- The actual point map into the coefficient-pushout extension. -/
def torsorPushoutSection (U : Cᵒᵖ) (t : P.carrier.obj.obj U) :
    (torsorPushout P q).carrier.obj.obj U :=
  ⟨(pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P ≫ q)).hom.app U
    (torsorGenerator P U t), by
    have h := congrArg (fun r => r.hom.app U (torsorGenerator P U t))
      (CategoryTheory.Abelian.ExtensionPushout.inl_projection (torsorAugmentationComplex P)
        (torsorDifferenceSheafMap P ≫ q))
    exact h.trans (torsorGenerator_augmentation P U t)⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The canonical difference map is the adjoint extension of its explicit
presheaf formula. -/
theorem torsorDifferenceSheafMap_unit :
    toSheafify J (torsorKernelPresheaf P) ≫
      (torsorDifferenceSheafMap P).hom = torsorKernelDifference P := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{w}
  change adj.homEquiv _ _ ((adj.homEquiv _ _).symm (torsorKernelDifference P)) = _
  exact (adj.homEquiv _ _).apply_symm_apply _

/-- Positive transport gives the relation `[a+t]-[t] ↦ a` after sheafification. -/
theorem torsorPushoutSection_equivariant (U : Cᵒᵖ)
    (a : L.obj.obj U) (t : P.carrier.obj.obj U) :
    torsorPushoutSection P q U (P.action U a t) =
      (torsorPushout P q).action U (q.hom.app U a) (torsorPushoutSection P q U t) := by
  let := P.sectionAction U
  let x := AddAction.TorsorAugmentation.generatorDifference (P.action U a t) t
  let k := (toSheafify J (torsorKernelPresheaf P)).app U x
  have hd : (torsorDifferenceSheafMap P).hom.app U k = a := by
    have h := congrArg (fun r => r.app U x) (torsorDifferenceSheafMap_unit P)
    change (torsorDifferenceSheafMap P).hom.app U k =
      AddAction.TorsorAugmentation.kernelDifference (P.unique_transport U) x at h
    rw [h]
    exact (AddAction.TorsorAugmentation.kernelDifference_generatorDifference _ _ _).trans
      (AddAction.TorsorAugmentation.difference_action _ a t)
  have hi : (torsorKernelSheafInclusion P).hom.app U k =
      torsorGenerator P U (P.action U a t) - torsorGenerator P U t := by
    have h := congrArg (fun r => r.app U x)
      (toSheafify_naturality J (torsorKernelInclusion P))
    change (toSheafify J (torsorFreePresheaf P)).app U
      (FreeAbelianGroup.of (P.action U a t) - FreeAbelianGroup.of t) =
        (torsorKernelSheafInclusion P).hom.app U k at h
    exact h.symm.trans (map_sub _ _ _)
  have hc := congrArg (fun r => r.hom.app U k)
    (pushout.condition (f := torsorKernelSheafInclusion P) (g := torsorDifferenceSheafMap P ≫ q))
  change (pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P ≫ q)).hom.app U
      ((torsorKernelSheafInclusion P).hom.app U k) =
    (pushout.inr (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P ≫ q)).hom.app U
      (q.hom.app U ((torsorDifferenceSheafMap P).hom.app U k)) at hc
  rw [hd, hi, map_sub] at hc
  apply Subtype.ext
  change (_ : (torsorCoefficientExtension P q).X₂.obj.obj U) = _
  exact sub_eq_iff_eq_add.mp hc

/-- The canonical coefficient-relative map into the actual pushout torsor. -/
def torsorPushoutMap : Torsor.Hom q P (torsorPushout P q) where
  map := ⟨{
    app U := TypeCat.ofHom (fun t => torsorPushoutSection P q U t)
    naturality {U V} f := by
      ext t
      apply Subtype.ext
      change (pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P ≫ q)).hom.app V
          (torsorGenerator P V (P.carrier.obj.map f t)) =
        (torsorCoefficientExtension P q).X₂.obj.map f
          ((pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P ≫ q)).hom.app U
            (torsorGenerator P U t))
      rw [← torsorGenerator_naturality]
      exact ConcreteCategory.congr_hom
        ((pushout.inl (torsorKernelSheafInclusion P) (torsorDifferenceSheafMap P ≫
          q)).hom.naturality f)
        (torsorGenerator P U t) }⟩
  equivariant := torsorPushoutSection_equivariant P q

section ExtClass
variable [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- Coefficient pushout has exactly the coefficient-change Ext class. -/
theorem torsorExtClass_pushout :
    torsorExtClass (torsorPushout P q) = H.map q 1 (torsorExtClass P) :=
  (torsorExtClass_naturality (torsorPushoutMap P q)).symm

end ExtClass

/-- The original torsor maps canonically to the one-fibre of its constructed extension. -/
noncomputable def torsorCanonicalExtensionMap (P : Torsor L) :
    Torsor.Hom (𝟙 L) P
      (extensionFiberTorsor (torsorExtension P) (constantIntegerOne J)
        (torsorExtension_shortExact P)) := by
  have h : torsorPushout P (𝟙 L) =
      extensionFiberTorsor (torsorExtension P) (constantIntegerOne J)
        (torsorExtension_shortExact P) := by
    unfold torsorPushout torsorCoefficientExtension
    simp only [torsorAugmentationComplex]
    rfl
  exact h ▸ torsorPushoutMap P (𝟙 L)

/-- The canonical extension's augmentation-one fibre recovers the actual torsor. -/
noncomputable def torsorCanonicalExtensionIso (P : Torsor L) :
    Torsor.Iso P (extensionFiberTorsor (torsorExtension P) (constantIntegerOne J)
      (torsorExtension_shortExact P)) :=
  (torsorCanonicalExtensionMap P).toIso

end CategoryTheory.Sheaf
