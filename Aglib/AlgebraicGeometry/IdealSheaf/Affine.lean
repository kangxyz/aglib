/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Modules
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Morphisms
public import Aglib.Algebra.Category.ModuleCat.KernelBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Spec
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation

/-!
# Actual spectral ideal modules and ring kernels

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FlatIdealBaseChange.lean`, SHA-256
  `52ad81197b39689c02c7f936d7b8987c9dac2695568d56796cdb1c43743a6864`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `docs/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
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
namespace AlgebraicGeometry.Scheme.Hom

variable {R : CommRingCat.{u}} {M N : ModuleCat R}

/-- The actual kernel ideal module of a spectral morphism is quasicoherent. -/
instance affineIdeal_isQuasicoherent {S : CommRingCat.{u}} (φ : R ⟶ S) :
    (idealModule (Spec.map φ)).IsQuasicoherent := by
  let : (SheafOfModules.unit.{u} (Spec R).ringCatSheaf).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  let : (SheafOfModules.unit.{u} (Spec S).ringCatSheaf).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  let : ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (SheafOfModules.unit.{u} (Spec S).ringCatSheaf)).IsQuasicoherent :=
    isQuasicoherent_pushforward φ _
  exact affineQuasicoherentKernel (structureModuleMap (Spec.map φ))

/-- Global sections of the pushed spectral structure module, with its actual restricted scalars. -/
def affineStructurePushforwardΓIso {S : CommRingCat.{u}} (φ : R ⟶ S) :
    (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj
          (SheafOfModules.unit (Spec S).ringCatSheaf)) ≅
      (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) :=
  (pushforwardGlobalSectionsIso φ).app (tilde (ModuleCat.of S S)) ≪≫
    (ModuleCat.restrictScalars φ.hom).mapIso (tilde.isoTop (ModuleCat.of S S)).symm

theorem affineStructureMap_Γ {S : CommRingCat.{u}} (φ : R ⟶ S) :
    (tilde.isoTop (ModuleCat.of R R)).hom ≫
      (moduleSpecΓFunctor (R := R)).map (structureModuleMap (Spec.map φ)) ≫
        (affineStructurePushforwardΓIso φ).hom = ModuleCat.ringHomModuleMap φ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (tilde.isoTop (ModuleCat.of S S)).inv
      ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r)) = φ r
  have h := congrArg (fun f : R ⟶ (Spec S).presheaf.obj (op ⊤) ↦ f r)
    ((Scheme.ΓSpecIso_inv_naturality φ).symm)
  change (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) =
    (Scheme.ΓSpecIso S).inv (φ r) at h
  rw [h]
  exact (tilde.isoTop (ModuleCat.of S S)).hom_inv_id_apply (φ r)

/-- The actual spectral ideal global sections identify with the kernel of the original ring map. -/
def affineIdealΓKernelIso {S : CommRingCat.{u}} (φ : R ⟶ S) :
    ModuleCat.of R (RingHom.ker φ.hom) ≅
      kernel ((moduleSpecΓFunctor (R := R)).map (structureModuleMap (Spec.map φ))) :=
  (ModuleCat.kernelIsoKer (ModuleCat.ringHomModuleMap φ)).symm ≪≫
    kernel.mapIso (ModuleCat.ringHomModuleMap φ)
      ((moduleSpecΓFunctor (R := R)).map (structureModuleMap (Spec.map φ)))
      (tilde.isoTop (ModuleCat.of R R)) (affineStructurePushforwardΓIso φ).symm
      (by
        apply (cancel_mono (affineStructurePushforwardΓIso φ).hom).mp
        simpa only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
          (affineStructureMap_Γ φ).symm)

@[reassoc]
theorem affineIdealΓKernelIso_hom_ι {S : CommRingCat.{u}} (φ : R ⟶ S) :
    (affineIdealΓKernelIso φ).hom ≫
        kernel.ι ((moduleSpecΓFunctor (R := R)).map (structureModuleMap (Spec.map φ))) =
      ModuleCat.ofHom (RingHom.ker φ.hom).subtype ≫ (tilde.isoTop (ModuleCat.of R R)).hom := by
  simp only [affineIdealΓKernelIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    kernel.mapIso_hom, kernel.map, kernel.lift_ι]
  rw [← Category.assoc, ModuleCat.kernelIsoKer_inv_kernel_ι]
  rfl

/-- Sheafification of the original ring-kernel module is the actual spectral ideal module. -/
def affineIdealIso {S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde (ModuleCat.of R (RingHom.ker φ.hom)) ≅ idealModule (Spec.map φ) := by
  let : (SheafOfModules.unit.{u} (Spec R).ringCatSheaf).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  let : (SheafOfModules.unit.{u} (Spec S).ringCatSheaf).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  let : ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (SheafOfModules.unit.{u} (Spec S).ringCatSheaf)).IsQuasicoherent :=
    isQuasicoherent_pushforward φ _
  exact (tilde.functor R).mapIso (affineIdealΓKernelIso φ) ≪≫
    affineQuasicoherentKernelIso (structureModuleMap (Spec.map φ))

@[reassoc]
theorem affineIdealIso_hom_inclusion {S : CommRingCat.{u}} (φ : R ⟶ S) :
    (affineIdealIso φ).hom ≫ idealInclusion (Spec.map φ) =
      tilde.map (ModuleCat.ofHom (RingHom.ker φ.hom).subtype) := by
  simp only [affineIdealIso, Iso.trans_hom, Functor.mapIso_hom, idealInclusion,
    Category.assoc, affineQuasicoherentKernelIso_hom_ι]
  change (tilde.functor R).map (affineIdealΓKernelIso φ).hom ≫
    (tilde.functor R).map (kernel.ι ((moduleSpecΓFunctor (R := R)).map
      (structureModuleMap (Spec.map φ)))) ≫
    Scheme.Modules.fromTildeΓ (R := R) (SheafOfModules.unit (Spec R).ringCatSheaf) = _
  rw [← Category.assoc, ← Functor.map_comp, affineIdealΓKernelIso_hom_ι,
    Functor.map_comp, Category.assoc]
  have h := (tilde.adjunction (R := R)).left_triangle_components (ModuleCat.of R R)
  change (tilde.functor R).map (tilde.isoTop (ModuleCat.of R R)).hom ≫
    Scheme.Modules.fromTildeΓ (R := R) (SheafOfModules.unit (Spec R).ringCatSheaf) = 𝟙 _ at h
  rw [h, Category.comp_id]
  rfl

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

/-- A closed spectral ideal is finitely generated when the ambient algebra
and its quotient are finitely presented over the same base. -/
theorem spectralIdeal_fg {R A B : CommRingCat.{u}}
    (ψ : R ⟶ A) (φ : A ⟶ B) [IsClosedImmersion (Spec.map φ)]
    [LocallyOfFinitePresentation (Spec.map ψ)]
    [LocallyOfFinitePresentation (Spec.map φ ≫ Spec.map ψ)] :
    (RingHom.ker φ.hom).FG := by
  have hA := (LocallyOfFinitePresentation.SpecMap_iff ψ).mp inferInstance
  have hB : (ψ ≫ φ).hom.FinitePresentation :=
    (LocallyOfFinitePresentation.SpecMap_iff (ψ ≫ φ)).mp
      (by simpa only [Spec.map_comp] using
        (inferInstance : LocallyOfFinitePresentation (Spec.map φ ≫ Spec.map ψ)))
  algebraize [ψ.hom, φ.hom, (ψ ≫ φ).hom]
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FinitePresentation R A := hA
  let : Algebra.FinitePresentation R B := hB
  exact Algebra.FinitePresentation.ker_fG_of_surjective (IsScalarTower.toAlgHom R A B)
    (IsClosedImmersion.surjective_of_specMap φ)

end AlgebraicGeometry.Scheme.Hom
end
