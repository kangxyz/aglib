/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Torsors
public import Aglib.CategoryTheory.Abelian.ExtensionPushout
public import Aglib.Algebra.Group.Action.TorsorAugmentation
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Algebra.Category.Grp.Kernels
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# The torsor augmentation for the canonical Ext class

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

This implements the actual free-abelian-sheaf augmentation used in Stacks
03AJ, Lemma 21.4.3. A canonical Ext class requires the augmentation-kernel
map and pushout extension; no torsor/H¹ bijectivity is assumed here.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleH1
universe u
attribute [local instance] hasSheafifyLarge
variable {X : Scheme.{u}} {L : AbelianSheaf.{u, u + 1} X}

/-- The free abelian presheaf on the actual torsor sheaf. -/
def torsorFreePresheaf (P : Torsor L) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  P.carrier.obj ⋙ AddCommGrpCat.free

/-- Augmentation assigns one to every torsor section. -/
def torsorAugmentationPresheaf (P : Torsor L) :
    torsorFreePresheaf P ⟶ (Functor.const X.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) where
  app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun _ => (1 : ULift.{u + 1} ℤ)))
  naturality {U V} f := by
    ext t
    simp only [torsorFreePresheaf, Functor.comp_map, AddCommGrpCat.free_map,
      Functor.const_obj_map, AddCommGrpCat.comp_apply]
    exact (FreeAbelianGroup.lift_comp _ (fun _ => (1 : ULift.{u + 1} ℤ)) t).symm

/-- The free abelian sheaf on the torsor. -/
def torsorFreeSheaf (P : Torsor L) : AbelianSheaf.{u, u + 1} X :=
  (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj (torsorFreePresheaf P)

/-- The augmentation of the actual free abelian sheaf. -/
def torsorAugmentation (P : Torsor L) : torsorFreeSheaf P ⟶
    (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map
    (torsorAugmentationPresheaf P)

/-- Local nonemptiness makes augmentation locally surjective. -/
instance torsorAugmentationPresheaf_locallySurjective (P : Torsor L) :
    Presheaf.IsLocallySurjective (Scheme.smallEtaleTopology X)
      (torsorAugmentationPresheaf P) where
  imageSieve_mem {U} z := by
    refine (Scheme.smallEtaleTopology X).superset_covering ?_ (P.locally_nonempty U)
    rintro V f ⟨t⟩
    refine ⟨z.down • FreeAbelianGroup.of t, ?_⟩
    change FreeAbelianGroup.lift (fun _ => (1 : ULift.{u + 1} ℤ))
      (z.down • FreeAbelianGroup.of t) = z
    simp only [map_zsmul, FreeAbelianGroup.lift_apply_of, zsmul_eq_mul, mul_one]
    apply ULift.ext
    simp

/-- Sheafification preserves local surjectivity of the torsor augmentation. -/
instance torsorAugmentation_locallySurjective (P : Torsor L) :
    Sheaf.IsLocallySurjective (torsorAugmentation P) := by
  let J := Scheme.smallEtaleTopology X
  let a := torsorAugmentationPresheaf P
  have : Presheaf.IsLocallySurjective J (a ≫ toSheafify J _) := by
    infer_instance
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (toSheafify_naturality J a).symm

/-- The augmentation of a locally nonempty torsor is an epimorphism. -/
instance torsorAugmentation_epi (P : Torsor L) : Epi (torsorAugmentation P) := by
  infer_instance

/-- The augmentation is the universe lift of the ordinary integer augmentation. -/
theorem torsorAugmentationPresheaf_apply (P : Torsor L) (U : X.Etaleᵒᵖ)
    (x : FreeAbelianGroup (P.carrier.obj.obj U)) :
    (torsorAugmentationPresheaf P).app U x =
      ULift.up (AddAction.TorsorAugmentation.augmentation _ x) := by
  exact FreeAbelianGroup.lift_comp_apply x (fun _ => (1 : ℤ))
    (AddEquiv.ulift : ULift.{u + 1} ℤ ≃+ ℤ).symm.toAddMonoidHom

/-- The actual augmentation kernels, objectwise, with restriction maps. -/
def torsorKernelPresheaf (P : Torsor L) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
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

/-- The augmentation-kernel inclusion composes to zero. -/
theorem torsorKernelInclusion_augmentation (P : Torsor L) :
    torsorKernelInclusion P ≫ torsorAugmentationPresheaf P = 0 := by
  ext U x
  change (torsorAugmentationPresheaf P).app U x.val = 0
  rw [torsorAugmentationPresheaf_apply, x.property]
  rfl

/-- The explicit presheaf kernel identifies with the concrete kernel at each object. -/
def torsorKernelPointIso (P : Torsor L) (U : X.Etaleᵒᵖ) :
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
def torsorKernelSheaf (P : Torsor L) : AbelianSheaf.{u, u + 1} X :=
  (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
    (torsorKernelPresheaf P)

/-- The morphism from the sheafified torsor augmentation kernel to the free abelian
sheaf of the torsor, obtained by sheafifying `torsorKernelInclusion P`. -/
def torsorKernelSheafInclusion (P : Torsor L) : torsorKernelSheaf P ⟶ torsorFreeSheaf P :=
  (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map
    (torsorKernelInclusion P)

/-- The canonical torsor-difference morphism from the actual sheaf kernel. -/
def torsorDifferenceSheafMap (P : Torsor L) : torsorKernelSheaf P ⟶ L :=
  ((sheafificationAdjunction (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).homEquiv
    (torsorKernelPresheaf P) L).symm (torsorKernelDifference P)

theorem torsorKernelSheafInclusion_augmentation (P : Torsor L) :
    torsorKernelSheafInclusion P ≫ torsorAugmentation P = 0 := by
  change (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map _ ≫
    (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map _ = 0
  rw [← Functor.map_comp, torsorKernelInclusion_augmentation, Functor.map_zero]

/-- The augmentation short complex of the actual free abelian sheaf. -/
def torsorAugmentationComplex (P : Torsor L) : ShortComplex (AbelianSheaf.{u, u + 1} X) :=
  ShortComplex.mk (torsorKernelSheafInclusion P) (torsorAugmentation P)
    (torsorKernelSheafInclusion_augmentation P)

/-- Exact sheafification transports the proved presheaf kernel universal property. -/
def torsorKernelSheafIsLimit (P : Torsor L) :
    IsLimit (KernelFork.ofι (torsorKernelSheafInclusion P)
      (torsorKernelSheafInclusion_augmentation P)) :=
  KernelFork.mapIsLimit _ (torsorKernelIsLimit P)
    (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1})

/-- The torsor augmentation sequence is short exact. -/
theorem torsorAugmentation_shortExact (P : Torsor L) :
    (torsorAugmentationComplex P).ShortExact where
  exact := (torsorAugmentationComplex P).exact_of_f_is_kernel (torsorKernelSheafIsLimit P)
  mono_f := mono_of_isLimit_fork (torsorKernelSheafIsLimit P)
  epi_g := torsorAugmentation_epi P

/-- The actual pushout extension of constant ℤ by the coefficient sheaf. -/
def torsorExtension (P : Torsor L) : ShortComplex (AbelianSheaf.{u, u + 1} X) :=
  CategoryTheory.Abelian.ExtensionPushout.complex (torsorAugmentationComplex P)
    (torsorDifferenceSheafMap P)

/-- Exactness of the canonical torsor extension is proved. -/
theorem torsorExtension_shortExact (P : Torsor L) : (torsorExtension P).ShortExact :=
  CategoryTheory.Abelian.ExtensionPushout.shortExact _ _ (torsorAugmentation_shortExact P)

section ExtClass
universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The canonical torsor-to-Ext class, constructed from the genuine pushout
extension of Stacks 03AJ, with the `[s]-[t]` positive transport convention. -/
def torsorExtClass (P : Torsor L) : H1Etale X L :=
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

/-- The global section `1` of the actual constant integer sheaf. -/
def constantIntegerOne (X : Scheme.{u}) :
    ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).obj.obj (op (etaleTerminal X)) :=
  (toSheafify (Scheme.smallEtaleTopology X)
    ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
      (op (etaleTerminal X)) (ULift.up 1)

/-- The identity Ext⁰ class is exactly the global integer section `1`. -/
theorem constantIntegerOne_identity :
    Sheaf.H.equiv₀
      ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      (etaleTerminalIsTerminal X) (Abelian.Ext.mk₀ (𝟙 _)) = constantIntegerOne X := by
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply]
  rw [show Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ (𝟙 _)) = 𝟙 _ from
    Abelian.Ext.addEquiv₀.apply_symm_apply _]
  rfl

/-- The constructed class is the connecting image of the actual section `1`,
precisely the extension/boundary construction in Stacks 03AJ. -/
theorem torsorExtClass_boundary_one (P : Torsor L) :
    Sheaf.H.δ (torsorExtension_shortExact P) 0 1 rfl
      ((Sheaf.H.equiv₀ (torsorExtension P).X₃ (etaleTerminalIsTerminal X)).symm
        (constantIntegerOne X)) = torsorExtClass P := by
  have h : (Sheaf.H.equiv₀ (torsorExtension P).X₃ (etaleTerminalIsTerminal X)).symm
      (constantIntegerOne X) = Abelian.Ext.mk₀ (𝟙 (torsorExtension P).X₃) := by
    apply (Sheaf.H.equiv₀ (torsorExtension P).X₃ (etaleTerminalIsTerminal X)).injective
    rw [AddEquiv.apply_symm_apply]
    exact constantIntegerOne_identity.symm
  rw [h]
  exact torsorExtClass_boundary P

end ExtClass
end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 4ca9dbdef62cf0371d7571492313b359c02aafe74be5c8906ccc5aed3ef101a3.
Definitions, hypotheses and universes are retained modulo native names. -/
