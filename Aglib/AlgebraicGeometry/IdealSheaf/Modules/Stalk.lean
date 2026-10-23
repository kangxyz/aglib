/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Modules
public import Aglib.AlgebraicGeometry.IdealSheaf.Colon
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic

/-!
# The actual ideal-module stalk and the original stalk ideal

The comparison sends the germ of an ideal-module section to the germ of its
original inclusion in the structure sheaf. For a quasi-compact morphism its
image is the original `ker.stalkIdeal`. In particular the comparison applies
to every closed immersion, with no Noetherian or rank hypothesis.

The current consumer is the Cartier section/fibre criterion.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The additive comparison underlying the original structure-module stalk. -/
def unitModuleStalkAddIso (X : Scheme.{u}) (x : X) :
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj (X.presheaf.stalk x) :=
  (preservesColimitIso (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    ((OpenNhds.inclusion x).op ⋙ X.presheaf)).symm

/-- The additive comparison retains each original germ. -/
theorem unitModuleStalkAddIso_germ (X : Scheme.{u}) (x : X)
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    (unitModuleStalkAddIso X x).hom
        ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.germ U x hx a) =
      X.presheaf.germ U x hx a := by
  exact ConcreteCategory.congr_hom
    (ι_preservesColimitIso_inv (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
      ((OpenNhds.inclusion x).op ⋙ X.presheaf) (op ⟨U, hx⟩)) a

/-- The actual structure-module stalk is the original local ring, through
the canonical comparison for the forgetful functor and filtered colimits. -/
def unitModuleStalkEquiv (X : Scheme.{u}) (x : X) :
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x where
  __ := (unitModuleStalkAddIso X x).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    obtain ⟨U, hx, a, s, rfl, rfl⟩ :=
      exists_germ_smul_representatives X x (SheafOfModules.unit X.ringCatSheaf) r m
    erw [← _root_.PresheafOfModules.germ_smul]
    change (show X.presheaf.stalk x from (unitModuleStalkAddIso X x).hom
        ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.germ
          U x hx (a * (show Γ(X, U) from s)))) =
      X.presheaf.germ U x hx a * (show X.presheaf.stalk x from
        (unitModuleStalkAddIso X x).hom
          ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.germ U x hx s))
    exact (unitModuleStalkAddIso_germ X x U hx (a * (show Γ(X, U) from s))).trans
      ((map_mul (X.presheaf.germ U x hx).hom a s).trans
        (congrArg (fun t : X.presheaf.stalk x ↦ X.presheaf.germ U x hx a * t)
          (unitModuleStalkAddIso_germ X x U hx s).symm))

/-- The canonical unit-stalk comparison retains every original germ. -/
@[simp]
theorem unitModuleStalkEquiv_germ (X : Scheme.{u}) (x : X)
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    unitModuleStalkEquiv X x
        ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.germ U x hx a) =
      X.presheaf.germ U x hx a :=
  unitModuleStalkAddIso_germ X x U hx a

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules

variable {Z X : Scheme.{u}}

/-- The original ideal inclusion, on the native module stalk and original
local ring. -/
def idealModuleStalkInclusion (i : Z ⟶ X) (x : X) :
    (idealModule i).presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  (unitModuleStalkEquiv X x).toLinearMap.comp
    ((moduleStalk X x).map (idealInclusion i)).hom

/-- The actual stalk inclusion sends an ideal-section germ to the original
structure-sheaf germ of its inclusion. -/
@[simp]
theorem idealModuleStalkInclusion_germ (i : Z ⟶ X) (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(idealModule i, U)) :
    idealModuleStalkInclusion i x ((idealModule i).presheaf.germ U x hx s) =
      X.presheaf.germ U x hx ((idealInclusion i).app U s) := by
  change unitModuleStalkEquiv X x
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (idealInclusion i).mapPresheaf
      ((idealModule i).presheaf.germ U x hx s)) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, unitModuleStalkEquiv_germ]
  rfl

/-- Injectivity is inherited from the original kernel inclusion. -/
theorem idealModuleStalkInclusion_injective (i : Z ⟶ X) (x : X) :
    Function.Injective (idealModuleStalkInclusion i x) :=
  (unitModuleStalkEquiv X x).injective.comp
    ((ModuleCat.mono_iff_injective ((moduleStalk X x).map (idealInclusion i))).mp
      inferInstance)

/-- For a quasi-compact morphism, the image of the original ideal-module
stalk inclusion is precisely its original quasi-coherent stalk ideal. -/
theorem idealModuleStalkInclusion_range (i : Z ⟶ X) [QuasiCompact i] (x : X) :
    (idealModuleStalkInclusion i x).range = i.ker.stalkIdeal x := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    obtain ⟨U, hxU, s, rfl⟩ := (idealModule i).presheaf.exists_germ_eq m
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
    rw [← (idealModule i).presheaf.germ_res_apply (homOfLE hVU) x hxV s,
      idealModuleStalkInclusion_germ]
    rw [i.ker.stalkIdeal_eq_map ⟨V, hV⟩ x hxV]
    apply Ideal.mem_map_of_mem
    rw [i.ker_apply ⟨V, hV⟩]
    erw [← idealSectionsEquiv_val]
    exact (idealSectionsEquiv i V _).property
  · apply iSup_le
    intro U
    apply iSup_le
    intro hx
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have ha' : a ∈ RingHom.ker (i.app U.1).hom := by
      simpa only [i.ker_apply U] using ha
    let s := (idealSectionsEquiv i U.1).symm ⟨a, ha'⟩
    refine ⟨(idealModule i).presheaf.germ U.1 x hx s, ?_⟩
    rw [idealModuleStalkInclusion_germ]
    have hs := idealSectionsEquiv_val i U.1 s
    simp only [s, LinearEquiv.apply_symm_apply] at hs
    exact congrArg (X.presheaf.germ U.1 x hx) hs.symm

/-- The canonical linear identification of the actual ideal-module stalk
with the original stalk ideal. -/
def idealModuleStalkEquiv (i : Z ⟶ X) [QuasiCompact i] (x : X) :
    (idealModule i).presheaf.stalk x ≃ₗ[X.presheaf.stalk x] i.ker.stalkIdeal x :=
  LinearEquiv.ofBijective
    ((idealModuleStalkInclusion i x).codRestrict (i.ker.stalkIdeal x) (fun m ↦ by
      rw [← idealModuleStalkInclusion_range i x]
      exact ⟨m, rfl⟩))
    ⟨fun _ _ h ↦ idealModuleStalkInclusion_injective i x (congrArg Subtype.val h), by
      intro a
      have ha : a.val ∈ (idealModuleStalkInclusion i x).range := by
        rw [idealModuleStalkInclusion_range i x]
        exact a.property
      obtain ⟨m, hm⟩ := ha
      exact ⟨m, Subtype.ext hm⟩⟩

/-- The comparison preserves the actual inclusion, rather than choosing a
different identification of the ideal with an abstract line. -/
@[simp]
theorem idealModuleStalkEquiv_val (i : Z ⟶ X) [QuasiCompact i] (x : X)
    (m : (idealModule i).presheaf.stalk x) :
    (idealModuleStalkEquiv i x m).val = idealModuleStalkInclusion i x m := rfl

/-- In particular it preserves the original section and its actual germ. -/
theorem idealModuleStalkEquiv_germ_val (i : Z ⟶ X) [QuasiCompact i] (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(idealModule i, U)) :
    (idealModuleStalkEquiv i x ((idealModule i).presheaf.germ U x hx s)).val =
      X.presheaf.germ U x hx ((idealInclusion i).app U s) :=
  idealModuleStalkInclusion_germ i x U hx s

end AlgebraicGeometry.Scheme.Hom
