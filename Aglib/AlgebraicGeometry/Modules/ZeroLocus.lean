/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Modules
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Morphisms
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Native image-ideal subschemes of module-to-unit maps

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/ZeroLocus.lean`, SHA-256
  `965a9542a747894891b7cc04c235143b80984b77c931144b0b17f93d36a2c820`.

Actual objects, maps, universes and stated conditions are retained.
Native proof validation is pending the coordinated build.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open LinearMap

section
namespace AlgebraicGeometry.Scheme.Modules.Hom

variable {X : Scheme.{u}} {M : X.Modules}
variable (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

/-- The image ideal of the actual module-to-unit map on the specified open. -/
def sectionImageIdeal (U : X.Opens) : Ideal Γ(X,U) :=
  LinearMap.range (φ.val.app (op U)).hom

/-- The native ideal-sheaf data from the section image ideals; its image identification requires
localization. -/
def imageIdealData : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals (fun U ↦ Hom.sectionImageIdeal φ U.val)

/-- The explicit basic-open localization condition on the actual section image ideals. -/
def ImageIdealLocalizes : Prop :=
  ∀ (U : X.affineOpens) (s : Γ(X,U)),
    (Hom.sectionImageIdeal φ U.val).map (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom =
      Hom.sectionImageIdeal φ (X.affineBasicOpen s).val

theorem imageIdealData_eq (h : Hom.ImageIdealLocalizes φ) (U : X.affineOpens) :
    (Hom.imageIdealData φ).ideal U = Hom.sectionImageIdeal φ U.val := by
  let I : X.IdealSheafData := {
    ideal := fun V ↦ Hom.sectionImageIdeal φ V.val
    map_ideal_basicOpen := h }
  exact congrArg (fun J : X.IdealSheafData ↦ J.ideal U) (Scheme.IdealSheafData.ofIdeals_ideal I)

/-- The subscheme of the native image ideal data; actual image-kernel identification requires
localization. -/
def zeroScheme : Scheme.{u} := (Hom.imageIdealData φ).subscheme

/-- The inclusion of the native image-ideal subscheme; its kernel equation requires localization. -/
def zeroInclusion : Hom.zeroScheme φ ⟶ X := (Hom.imageIdealData φ).subschemeι

/-- The canonical image-ideal subscheme inclusion is a closed immersion. -/
instance zeroInclusion_isClosedImmersion : IsClosedImmersion (Hom.zeroInclusion φ) := by
  dsimp [Hom.zeroInclusion]; infer_instance

theorem zeroInclusion_kernel (h : Hom.ImageIdealLocalizes φ) (U : X.affineOpens) :
    RingHom.ker ((Hom.zeroInclusion φ).app U).hom = Hom.sectionImageIdeal φ U.val :=
  (Scheme.IdealSheafData.ker_subschemeι_app _ U).trans (Hom.imageIdealData_eq φ h U)

theorem zeroInclusion_annihilates (h : Hom.ImageIdealLocalizes φ) (U : X.affineOpens)
    (m : M.val.obj (op U.val)) :
    (Hom.zeroInclusion φ).app U ((φ.val.app (op U.val)) m) = 0 := by
  change (φ.val.app (op U.val)) m ∈ RingHom.ker ((Hom.zeroInclusion φ).app U).hom
  rw [Hom.zeroInclusion_kernel φ h U]
  exact ⟨m, rfl⟩

end AlgebraicGeometry.Scheme.Modules.Hom
end

section
namespace AlgebraicGeometry.Scheme.Modules.Hom

variable {X : Scheme.{u}} {M N : X.Modules}
variable (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

theorem zeroInclusion_annihilates_map (h : Hom.ImageIdealLocalizes φ) :
    φ ≫ structureModuleMap (Hom.zeroInclusion φ) = 0 := by
  apply moduleHom_ext_affine
  intro U
  ext m
  exact Hom.zeroInclusion_annihilates φ h U m

/-- The canonical factor into the actual zero-inclusion ideal under the explicit localization
condition. -/
def zeroIdealFactor (h : Hom.ImageIdealLocalizes φ) : M ⟶ idealModule (Hom.zeroInclusion φ) :=
  kernel.lift (structureModuleMap (Hom.zeroInclusion φ)) φ (Hom.zeroInclusion_annihilates_map φ h)

@[reassoc (attr := simp)] theorem zeroIdealFactor_inclusion (h : Hom.ImageIdealLocalizes φ) :
    Hom.zeroIdealFactor φ h ≫ idealInclusion (Hom.zeroInclusion φ) = φ := kernel.lift_ι _ _ _

end AlgebraicGeometry.Scheme.Modules.Hom
end

section
namespace AlgebraicGeometry.Scheme.Modules.Hom

variable {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
variable (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

theorem imageIdealLocalizes_of_isQuasicoherent : Hom.ImageIdealLocalizes φ := by
  intro U s
  let j := homOfLE (X.basicOpen_le s)
  let r := (X.presheaf.map j.op).hom
  change Ideal.map r (LinearMap.range (φ.val.app (op U.val)).hom) =
    LinearMap.range (φ.val.app (op (X.basicOpen s))).hom
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    rintro x ⟨m, rfl⟩
    refine ⟨M.val.map j.op m, ?_⟩
    exact PresheafOfModules.naturality_apply φ.val j.op m
  · rintro x ⟨m, rfl⟩
    obtain ⟨n, a, ha⟩ := affineSections_denominator U M s m
    have h := congrArg (φ.val.app (op (X.basicOpen s))) ha
    rw [_root_.map_smul] at h
    have h' : (r s)^n * (show Γ(X,X.basicOpen s) from (φ.val.app (op (X.basicOpen s))) m) =
        r ((φ.val.app (op U.val)) a) :=
      h.trans (PresheafOfModules.naturality_apply φ.val j.op a)
    have hm : r ((φ.val.app (op U.val)) a) ∈
        Ideal.map r (LinearMap.range (φ.val.app (op U.val)).hom) :=
      Ideal.mem_map_of_mem r ⟨a, rfl⟩
    have hs : IsUnit (r s) := by
      exact X.toRingedSpace.isUnit_res_basicOpen s
    rw [← h'] at hm
    exact (Ideal.unit_mul_mem_iff_mem _ (hs.pow n)).mp hm

end AlgebraicGeometry.Scheme.Modules.Hom
end

section
namespace AlgebraicGeometry.Scheme.Modules.Hom

variable {X : Scheme.{u}} {M : X.Modules}
variable (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

theorem zeroIdealFactor_isIso (h : Hom.ImageIdealLocalizes φ) [Mono φ] :
    IsIso (Hom.zeroIdealFactor φ h) := by
  have hb (U : X.affineOpens) : IsIso ((Hom.zeroIdealFactor φ h).app U.val) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · intro m n hmn
      have he := congrArg ((idealInclusion (Hom.zeroInclusion φ)).app U.val) hmn
      have hf (m : Γ(M,U.val)) :
          (idealInclusion (Hom.zeroInclusion φ)).app U.val ((Hom.zeroIdealFactor φ h).app U.val m) =
            φ.app U.val m :=
        congrArg (fun ψ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ↦
          ψ.app U.val m) (Hom.zeroIdealFactor_inclusion φ h)
      have hm : φ.app U.val m = φ.app U.val n := (hf m).symm.trans (he.trans (hf n))
      let ev : X.Modules ⥤ ModuleCat Γ(X,U) := SheafOfModules.evaluation X.ringCatSheaf (op U.val)
      have : PreservesLimits ev := inferInstanceAs
        (PreservesLimits (SheafOfModules.evaluation X.ringCatSheaf (op U.val)))
      exact (ModuleCat.mono_iff_injective (ev.map φ)).mp inferInstance hm
    · intro a
      have ha := (idealSectionsEquiv (Hom.zeroInclusion φ) U.val a).property
      have ha' : ((idealSectionsEquiv (Hom.zeroInclusion φ) U.val a) : Γ(X,U)) ∈
          Hom.sectionImageIdeal φ U.val :=
        (congrArg (fun I : Ideal Γ(X,U) ↦
          ((idealSectionsEquiv (Hom.zeroInclusion φ) U.val a) : Γ(X,U)) ∈ I)
          (Hom.zeroInclusion_kernel φ h U)).mp ha
      obtain ⟨m, hm⟩ := ha'
      refine ⟨m, ?_⟩
      apply (idealSectionsEquiv (Hom.zeroInclusion φ) U.val).injective
      apply Subtype.ext
      rw [idealSectionsEquiv_val, idealSectionsEquiv_val]
      have hf := congrArg (fun ψ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ↦
        ψ.app U.val m) (Hom.zeroIdealFactor_inclusion φ h)
      exact hf.trans (hm.trans (idealSectionsEquiv_val (Hom.zeroInclusion φ) U.val a))
  let ψ : (SheafOfModules.toSheaf X.ringCatSheaf).obj M ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj (idealModule (Hom.zeroInclusion φ)) :=
    (SheafOfModules.toSheaf X.ringCatSheaf).map (Hom.zeroIdealFactor φ h)
  have : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis
    (B := fun U : X.affineOpens ↦ U.val) (by simpa using X.isBasis_affineOpens) hb
  have : IsIso ((Scheme.Modules.toPresheaf X).map (Hom.zeroIdealFactor φ h)) :=
    inferInstanceAs (IsIso ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).map ψ))
  exact isIso_of_reflects_iso (Hom.zeroIdealFactor φ h) (Scheme.Modules.toPresheaf X)

end AlgebraicGeometry.Scheme.Modules.Hom
end
