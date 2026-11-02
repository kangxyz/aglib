/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Augmentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Torsors

/-! # The original etale torsor augmentation

The selected generic-site producer retains the original free presheaf,
augmentation kernel, difference map and pushout extension. This file supplies
the actual small-etale site and retains the terminal-section presentation of
integer one and of the degree-zero boundary formula.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
variable {X : Scheme.{u}} {L : AbelianSheaf.{u, u + 1} X}

/-- The free abelian presheaf on the actual torsor sheaf. -/
abbrev torsorFreePresheaf (P : Torsor L) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sheaf.torsorFreePresheaf P

/-- Augmentation assigns one to every torsor section. -/
abbrev torsorAugmentationPresheaf (P : Torsor L) :
    torsorFreePresheaf P ⟶ (Functor.const X.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  CategoryTheory.Sheaf.torsorAugmentationPresheaf P

/-- The free abelian sheaf on the torsor. -/
abbrev torsorFreeSheaf (P : Torsor L) : AbelianSheaf.{u, u + 1} X :=
  CategoryTheory.Sheaf.torsorFreeSheaf P

/-- The augmentation of the actual free abelian sheaf. -/
abbrev torsorAugmentation (P : Torsor L) : torsorFreeSheaf P ⟶
    (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  CategoryTheory.Sheaf.torsorAugmentation P

/-- Local nonemptiness makes augmentation locally surjective. -/
instance torsorAugmentationPresheaf_locallySurjective (P : Torsor L) :
    Presheaf.IsLocallySurjective (Scheme.smallEtaleTopology X)
      (torsorAugmentationPresheaf P) :=
  CategoryTheory.Sheaf.torsorAugmentationPresheaf_locallySurjective P

/-- Sheafification preserves local surjectivity of the torsor augmentation. -/
instance torsorAugmentation_locallySurjective (P : Torsor L) :
    Sheaf.IsLocallySurjective (torsorAugmentation P) :=
  CategoryTheory.Sheaf.torsorAugmentation_locallySurjective P

/-- The augmentation of a locally nonempty torsor is an epimorphism. -/
instance torsorAugmentation_epi (P : Torsor L) : Epi (torsorAugmentation P) :=
  CategoryTheory.Sheaf.torsorAugmentation_epi P

/-- The augmentation is the universe lift of the ordinary integer augmentation. -/
theorem torsorAugmentationPresheaf_apply (P : Torsor L) (U : X.Etaleᵒᵖ)
    (x : FreeAbelianGroup (P.carrier.obj.obj U)) :
    (torsorAugmentationPresheaf P).app U x =
      ULift.up (AddAction.TorsorAugmentation.augmentation _ x) :=
  CategoryTheory.Sheaf.torsorAugmentationPresheaf_apply P U x

/-- The actual augmentation kernels, objectwise, with restriction maps. -/
abbrev torsorKernelPresheaf (P : Torsor L) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sheaf.torsorKernelPresheaf P

/-- Inclusion of the augmentation kernel presheaf. -/
abbrev torsorKernelInclusion (P : Torsor L) : torsorKernelPresheaf P ⟶ torsorFreePresheaf P :=
  CategoryTheory.Sheaf.torsorKernelInclusion P

/-- The difference map is defined without choosing any global torsor section. -/
abbrev torsorKernelDifference (P : Torsor L) : torsorKernelPresheaf P ⟶ L.obj :=
  CategoryTheory.Sheaf.torsorKernelDifference P

/-- The augmentation-kernel inclusion composes to zero. -/
theorem torsorKernelInclusion_augmentation (P : Torsor L) :
    torsorKernelInclusion P ≫ torsorAugmentationPresheaf P = 0 :=
  CategoryTheory.Sheaf.torsorKernelInclusion_augmentation P

/-- The explicit presheaf kernel identifies with the concrete kernel at each object. -/
abbrev torsorKernelPointIso (P : Torsor L) (U : X.Etaleᵒᵖ) :
    (torsorKernelPresheaf P).obj U ≅
      AddCommGrpCat.of ((torsorAugmentationPresheaf P).app U).hom.ker :=
  CategoryTheory.Sheaf.torsorKernelPointIso P U

/-- The actual augmentation kernel universal property, not a kernel-shaped premise. -/
abbrev torsorKernelIsLimit (P : Torsor L) :
    IsLimit (KernelFork.ofι (torsorKernelInclusion P) (torsorKernelInclusion_augmentation P)) :=
  CategoryTheory.Sheaf.torsorKernelIsLimit P

/-- The sheafified augmentation kernel. -/
abbrev torsorKernelSheaf (P : Torsor L) : AbelianSheaf.{u, u + 1} X :=
  CategoryTheory.Sheaf.torsorKernelSheaf P

/-- The morphism from the sheafified torsor augmentation kernel to the free abelian
sheaf of the torsor, obtained by sheafifying `torsorKernelInclusion P`. -/
abbrev torsorKernelSheafInclusion (P : Torsor L) : torsorKernelSheaf P ⟶ torsorFreeSheaf P :=
  CategoryTheory.Sheaf.torsorKernelSheafInclusion P

/-- The canonical torsor-difference morphism from the actual sheaf kernel. -/
abbrev torsorDifferenceSheafMap (P : Torsor L) : torsorKernelSheaf P ⟶ L :=
  CategoryTheory.Sheaf.torsorDifferenceSheafMap P

theorem torsorKernelSheafInclusion_augmentation (P : Torsor L) :
    torsorKernelSheafInclusion P ≫ torsorAugmentation P = 0 :=
  CategoryTheory.Sheaf.torsorKernelSheafInclusion_augmentation P

/-- The augmentation short complex of the actual free abelian sheaf. -/
abbrev torsorAugmentationComplex (P : Torsor L) : ShortComplex (AbelianSheaf.{u, u + 1} X) :=
  CategoryTheory.Sheaf.torsorAugmentationComplex P

/-- Exact sheafification transports the proved presheaf kernel universal property. -/
abbrev torsorKernelSheafIsLimit (P : Torsor L) :
    IsLimit (KernelFork.ofι (torsorKernelSheafInclusion P)
      (torsorKernelSheafInclusion_augmentation P)) :=
  CategoryTheory.Sheaf.torsorKernelSheafIsLimit P

/-- The torsor augmentation sequence is short exact. -/
theorem torsorAugmentation_shortExact (P : Torsor L) :
    (torsorAugmentationComplex P).ShortExact :=
  CategoryTheory.Sheaf.torsorAugmentation_shortExact P

/-- The actual pushout extension of constant ℤ by the coefficient sheaf. -/
abbrev torsorExtension (P : Torsor L) : ShortComplex (AbelianSheaf.{u, u + 1} X) :=
  CategoryTheory.Sheaf.torsorExtension P

/-- Exactness of the canonical torsor extension is proved. -/
theorem torsorExtension_shortExact (P : Torsor L) : (torsorExtension P).ShortExact :=
  CategoryTheory.Sheaf.torsorExtension_shortExact P

/-- The original terminal-site value of the intrinsic integer-one global element. -/
def constantIntegerOne (X : Scheme.{u}) :
    ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).obj.obj (op (etaleTerminal X)) :=
  Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X) _
    (CategoryTheory.Sheaf.constantIntegerOne (Scheme.smallEtaleTopology X))

/-- The terminal-site presentation gives the same intrinsic integer-one arrow. -/
theorem constantIntegerOne_asGlobalPoint :
    (Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X)
      (underlyingSetSheaf ((constantSheaf (Scheme.smallEtaleTopology X)
        AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))).symm
      (constantIntegerOne X) =
        CategoryTheory.Sheaf.constantIntegerOne (Scheme.smallEtaleTopology X) :=
  (Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X) _).symm_apply_apply _

section ExtClass
universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The canonical torsor-to-Ext class, constructed from the genuine pushout
extension of Stacks 03AJ, with the `[s]-[t]` positive transport convention. -/
abbrev torsorExtClass (P : Torsor L) : H1Etale X L :=
  CategoryTheory.Sheaf.torsorExtClass P

/-- Equivalent coefficient-change description of the constructed pushout class. -/
theorem torsorExtClass_eq (P : Torsor L) :
    torsorExtClass P = (torsorAugmentation_shortExact P).extClass.comp
      (Abelian.Ext.mk₀ (torsorDifferenceSheafMap P)) (add_zero 1) :=
  CategoryTheory.Sheaf.torsorExtClass_eq P

/-- The class is the connecting image of the identity class of constant ℤ. -/
theorem torsorExtClass_boundary (P : Torsor L) :
    Sheaf.H.δ (torsorExtension_shortExact P) 0 1 rfl
      (Abelian.Ext.mk₀ (𝟙 (torsorExtension P).X₃)) = torsorExtClass P :=
  CategoryTheory.Sheaf.torsorExtClass_boundary P

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
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 4ca9dbdef62cf0371d7571492313b359c02aafe74be5c8906ccc5aed3ef101a3.
Definitions, hypotheses and universes are retained modulo native names. -/
