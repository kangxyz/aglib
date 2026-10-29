/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Basic
public import Aglib.CategoryTheory.Abelian.ExtensionPushout
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.Kernels
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-! # The actual torsor augmentation and its canonical extension

The free abelian presheaf, augmentation kernel, positive difference map and
pushout are the original constructors. Site, Hom, value and Ext universes
remain independent. Integer one is an intrinsic global element of the same
constant-integer sheaf; no terminal site object is required.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {L : Sheaf J AddCommGrpCat.{w}}

variable (J) in
/-- The actual constant lifted-integer sheaf used in native Ext cohomology. -/
abbrev constantIntegerSheaf : Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))

variable (J) in
/-- Integer one as an arrow from the actual terminal sheaf. -/
def constantIntegerOne :
    Topos.GlobalPoint (underlyingSetSheaf
      (constantIntegerSheaf J : Sheaf J AddCommGrpCat.{w})) where
  hom.app U := TypeCat.ofHom (fun _ =>
    (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ)))).app U
      (ULift.up 1))
  hom.naturality {U V} f := by
    ext x
    exact ConcreteCategory.congr_hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ)))).naturality f)
      (ULift.up 1)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Every component is the original sheafification-unit value of integer one. -/
@[simp] theorem constantIntegerOne_app (U : Cᵒᵖ) :
    (constantIntegerOne J).hom.app U PUnit.unit =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ)))).app U
        (ULift.up 1) := rfl

/-- The free abelian presheaf on the actual torsor sheaf. -/
def torsorFreePresheaf (P : Torsor L) : Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  P.carrier.obj ⋙ AddCommGrpCat.free

/-- Augmentation assigns one to every torsor section. -/
def torsorAugmentationPresheaf (P : Torsor L) :
    torsorFreePresheaf P ⟶ (Functor.const Cᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{w} ℤ)) where
  app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun _ => (1 : ULift.{w} ℤ)))
  naturality {U V} f := by
    ext t
    simp only [torsorFreePresheaf, Functor.comp_map, AddCommGrpCat.free_map,
      Functor.const_obj_map, AddCommGrpCat.comp_apply]
    exact (FreeAbelianGroup.lift_comp _ (fun _ => (1 : ULift.{w} ℤ)) t).symm

/-- The free abelian sheaf on the torsor. -/
def torsorFreeSheaf (P : Torsor L) : Sheaf J AddCommGrpCat.{w} :=
  (presheafToSheaf J AddCommGrpCat.{w}).obj (torsorFreePresheaf P)

/-- The augmentation of the actual free abelian sheaf. -/
def torsorAugmentation (P : Torsor L) : torsorFreeSheaf P ⟶
    (constantSheaf J AddCommGrpCat.{w}).obj
      (AddCommGrpCat.of (ULift.{w} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat.{w}).map
    (torsorAugmentationPresheaf P)

/-- Local nonemptiness makes augmentation locally surjective. -/
instance torsorAugmentationPresheaf_locallySurjective (P : Torsor L) :
    Presheaf.IsLocallySurjective J
      (torsorAugmentationPresheaf P) where
  imageSieve_mem {U} z := by
    refine J.superset_covering ?_ (P.locally_nonempty U)
    rintro V f ⟨t⟩
    refine ⟨z.down • FreeAbelianGroup.of t, ?_⟩
    change FreeAbelianGroup.lift (fun _ => (1 : ULift.{w} ℤ))
      (z.down • FreeAbelianGroup.of t) = z
    simp only [map_zsmul, FreeAbelianGroup.lift_apply_of, zsmul_eq_mul, mul_one]
    apply ULift.ext
    simp

/-- Sheafification preserves local surjectivity of the torsor augmentation. -/
instance torsorAugmentation_locallySurjective (P : Torsor L) :
    Sheaf.IsLocallySurjective (torsorAugmentation P) := by
  let a := torsorAugmentationPresheaf P
  have : Presheaf.IsLocallySurjective J (a ≫ toSheafify J _) := by
    infer_instance
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (toSheafify_naturality J a).symm

/-- The augmentation of a locally nonempty torsor is an epimorphism. -/
instance torsorAugmentation_epi (P : Torsor L) : Epi (torsorAugmentation P) := by
  infer_instance

omit [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The augmentation is the universe lift of the ordinary integer augmentation. -/
theorem torsorAugmentationPresheaf_apply (P : Torsor L) (U : Cᵒᵖ)
    (x : FreeAbelianGroup (P.carrier.obj.obj U)) :
    (torsorAugmentationPresheaf P).app U x =
      ULift.up (AddAction.TorsorAugmentation.augmentation _ x) := by
  exact FreeAbelianGroup.lift_comp_apply x (fun _ => (1 : ℤ))
    (AddEquiv.ulift : ULift.{w} ℤ ≃+ ℤ).symm.toAddMonoidHom

/-- The actual augmentation kernels, objectwise, with restriction maps. -/
def torsorKernelPresheaf (P : Torsor L) : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj U := AddCommGrpCat.of (AddAction.TorsorAugmentation.AugmentationKernel (P.carrier.obj.obj U))
  map f := AddCommGrpCat.ofHom (AddAction.TorsorAugmentation.kernelMap (P.carrier.obj.map f))
  map_id U := by
    ext x
    change FreeAbelianGroup.map (fun y => P.carrier.obj.map (𝟙 U) y) x.val = x.val
    rw [P.carrier.obj.map_id]
    exact FreeAbelianGroup.map_id_apply x.val
  map_comp f g := by
    ext x
    change FreeAbelianGroup.map (fun y => P.carrier.obj.map (f ≫ g) y) x.val =
      FreeAbelianGroup.map (fun y => P.carrier.obj.map g y)
        (FreeAbelianGroup.map (fun y => P.carrier.obj.map f y) x.val)
    rw [P.carrier.obj.map_comp]
    simpa only [types_comp_apply, Function.comp_def] using
      (FreeAbelianGroup.map_comp_apply
        (f := fun y => P.carrier.obj.map f y)
        (g := fun y => P.carrier.obj.map g y) x.val)

/-- Inclusion of the augmentation kernel presheaf. -/
def torsorKernelInclusion (P : Torsor L) : torsorKernelPresheaf P ⟶ torsorFreePresheaf P where
  app U := AddCommGrpCat.ofHom (AddAction.TorsorAugmentation.augmentation (P.carrier.obj.obj
    U)).ker.subtype
  naturality {U V} f := by ext x; rfl

/-- The difference map is defined without choosing any global torsor section. -/
def torsorKernelDifference (P : Torsor L) : torsorKernelPresheaf P ⟶ L.obj where
  app U := by
    let := P.sectionAction U
    exact AddCommGrpCat.ofHom (AddAction.TorsorAugmentation.kernelDifference (P.unique_transport U))
  naturality {U V} f := by
    let := P.sectionAction U
    let := P.sectionAction V
    ext x
    exact AddAction.TorsorAugmentation.kernelDifference_naturality (P.unique_transport U)
      (P.unique_transport V) (L.obj.map f).hom (P.carrier.obj.map f) (P.naturality f) x

omit [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The augmentation-kernel inclusion composes to zero. -/
theorem torsorKernelInclusion_augmentation (P : Torsor L) :
    torsorKernelInclusion P ≫ torsorAugmentationPresheaf P = 0 := by
  ext U x
  change (torsorAugmentationPresheaf P).app U x.val = 0
  rw [torsorAugmentationPresheaf_apply, x.property]
  rfl

/-- The explicit presheaf kernel identifies with the concrete kernel at each object. -/
def torsorKernelPointIso (P : Torsor L) (U : Cᵒᵖ) :
    (torsorKernelPresheaf P).obj U ≅
      AddCommGrpCat.of ((torsorAugmentationPresheaf P).app U).hom.ker :=
  AddEquiv.toAddCommGrpIso {
    toFun x := ⟨x.val, by
      change (torsorAugmentationPresheaf P).app U x.val = 0
      rw [torsorAugmentationPresheaf_apply, x.property]
      rfl⟩
    invFun x := ⟨x.val, by
      have h := congrArg ULift.down x.property
      change ((torsorAugmentationPresheaf P).app U x.val).down = 0 at h
      rw [torsorAugmentationPresheaf_apply] at h
      exact h⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl }

/-- The actual augmentation kernel universal property, not a kernel-shaped premise. -/
def torsorKernelIsLimit (P : Torsor L) :
    IsLimit (KernelFork.ofι (torsorKernelInclusion P) (torsorKernelInclusion_augmentation P)) := by
  refine evaluationJointlyReflectsLimits _ fun U =>
    (KernelFork.isLimitMapConeEquiv ..).2 ?_
  exact (AddCommGrpCat.kernelIsLimit ((torsorAugmentationPresheaf P).app U)).ofIsoLimit
    (Fork.ext (torsorKernelPointIso P U).symm (by ext x; rfl))

/-- The sheafified augmentation kernel. -/
def torsorKernelSheaf (P : Torsor L) : Sheaf J AddCommGrpCat.{w} :=
  (presheafToSheaf J AddCommGrpCat.{w}).obj
    (torsorKernelPresheaf P)

/-- The morphism from the sheafified torsor augmentation kernel to the free abelian
sheaf of the torsor, obtained by sheafifying `torsorKernelInclusion P`. -/
def torsorKernelSheafInclusion (P : Torsor L) : torsorKernelSheaf P ⟶ torsorFreeSheaf P :=
  (presheafToSheaf J AddCommGrpCat.{w}).map
    (torsorKernelInclusion P)

/-- The canonical torsor-difference morphism from the actual sheaf kernel. -/
def torsorDifferenceSheafMap (P : Torsor L) : torsorKernelSheaf P ⟶ L :=
  ((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv
    (torsorKernelPresheaf P) L).symm (torsorKernelDifference P)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
theorem torsorKernelSheafInclusion_augmentation (P : Torsor L) :
    torsorKernelSheafInclusion P ≫ torsorAugmentation P = 0 := by
  change (presheafToSheaf J AddCommGrpCat.{w}).map _ ≫
    (presheafToSheaf J AddCommGrpCat.{w}).map _ = 0
  rw [← Functor.map_comp, torsorKernelInclusion_augmentation, Functor.map_zero]

/-- The augmentation short complex of the actual free abelian sheaf. -/
def torsorAugmentationComplex (P : Torsor L) : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk (torsorKernelSheafInclusion P) (torsorAugmentation P)
    (torsorKernelSheafInclusion_augmentation P)

/-- Exact sheafification transports the proved presheaf kernel universal property. -/
def torsorKernelSheafIsLimit (P : Torsor L) :
    IsLimit (KernelFork.ofι (torsorKernelSheafInclusion P)
      (torsorKernelSheafInclusion_augmentation P)) :=
  KernelFork.mapIsLimit _ (torsorKernelIsLimit P)
    (presheafToSheaf J AddCommGrpCat.{w})

/-- The torsor augmentation sequence is short exact. -/
theorem torsorAugmentation_shortExact (P : Torsor L) :
    (torsorAugmentationComplex P).ShortExact where
  exact := (torsorAugmentationComplex P).exact_of_f_is_kernel (torsorKernelSheafIsLimit P)
  mono_f := mono_of_isLimit_fork (torsorKernelSheafIsLimit P)
  epi_g := torsorAugmentation_epi P

/-- The actual pushout extension of constant ℤ by the coefficient sheaf. -/
def torsorExtension (P : Torsor L) : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  CategoryTheory.Abelian.ExtensionPushout.complex (torsorAugmentationComplex P)
    (torsorDifferenceSheafMap P)

/-- Exactness of the canonical torsor extension is proved. -/
theorem torsorExtension_shortExact (P : Torsor L) : (torsorExtension P).ShortExact :=
  CategoryTheory.Abelian.ExtensionPushout.shortExact _ _ (torsorAugmentation_shortExact P)

section ExtClass
universe e
variable [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- The canonical torsor-to-Ext class, constructed from the genuine pushout
extension of Stacks 03AJ, with the `[s]-[t]` positive transport convention. -/
def torsorExtClass (P : Torsor L) : H L 1 :=
  (torsorExtension_shortExact P).extClass

/-- Equivalent coefficient-change description of the constructed pushout class. -/
theorem torsorExtClass_eq (P : Torsor L) :
    torsorExtClass P = (torsorAugmentation_shortExact P).extClass.comp
      (Abelian.Ext.mk₀ (torsorDifferenceSheafMap P)) (add_zero 1) :=
  (CategoryTheory.Abelian.ExtensionPushout.extClass _ _ (torsorAugmentation_shortExact P)).symm

/-- The class is the connecting image of the identity class of constant ℤ. -/
theorem torsorExtClass_boundary (P : Torsor L) :
    Sheaf.H.δ (torsorExtension_shortExact P) 0 1 rfl
      (Abelian.Ext.mk₀ (𝟙 (torsorExtension P).X₃)) = torsorExtClass P := by
  change (Abelian.Ext.mk₀ (𝟙 _)).comp _ (zero_add 1) = _
  exact Abelian.Ext.mk₀_id_comp _

end ExtClass
end CategoryTheory.Sheaf
