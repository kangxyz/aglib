/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineBoundedModule
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineReconstructionMapCoordinates
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompatiblePresentation

/-!
# The coherent affine reconstruction coefficient and original stage maps

Sheafification of the actual finite pullback gives the coherent coefficient.
Its maps to the algebraic target and to every original formal stage are
constructed from the original two pullback projections. Invertibility of the
resulting completion comparison is a subsequent reduction theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F : AdicSystem (Spec B) K}
  {H : (Spec B).CoherentSheaf} (α : F ⟶ (completionFunctor (Spec B) K).obj H)

/-- The reconstruction target uses the completed scalar action on its original formal sections. -/
local instance : Module (AdicCompletion (affineIdeal B K) B) F.affineFormalSections :=
  F.affineFormalSectionsModule

local instance : IsScalarTower B (AdicCompletion (affineIdeal B K) B) F.affineFormalSections :=
  F.affineSections_isCompatibleSystem.sectionsScalarTower

local instance : H.obj.IsQuasicoherent :=
  ((QuasiCoherent.affineLocallyFiniteType_spec_iff B H.obj).mp H.property).1

/-- Sheafification of the actual finite affine reconstruction module. -/
def affineReconstructionSheaf (t : ℕ) (h : AdicSystem.DefectsKilled K t α) :
    (Spec B).CoherentSheaf := by
  let P := ModuleCat.of B (affineReconstructionModule α)
  let : Module.Finite B P := affineReconstructionModule_finite α t h
  let e : P ≃ₗ[B] moduleSpecΓFunctor.obj (tilde P) :=
    (tilde.toTildeΓNatIso.app P).toLinearEquiv
  exact ⟨tilde P, (QuasiCoherent.affineLocallyFiniteType_spec_iff B _).mpr
    ⟨inferInstance, Module.Finite.equiv e⟩⟩

/-- The original second projection with its actual bundled module endpoints. -/
abbrev affineReconstructionTargetHom :
    ModuleCat.of B (affineReconstructionModule α) ⟶ moduleSpecΓFunctor.obj H.obj :=
  ModuleCat.ofHom (X := ModuleCat.of B (affineReconstructionModule α))
    (Y := moduleSpecΓFunctor.obj H.obj) (affineReconstructionModuleToTarget α)

/-- The original second projection followed by the original tilde counit. -/
def affineReconstructionSheafMap (t : ℕ) (h : AdicSystem.DefectsKilled K t α) :
    affineReconstructionSheaf α t h ⟶ H :=
  ObjectProperty.homMk
    (tilde.map (affineReconstructionTargetHom α) ≫ H.obj.fromTildeΓ)

/-- The original first projection followed by the original formal evaluation. -/
def affineReconstructionStageMap (n : ℕᵒᵖ) :
    affineReconstructionModule α →ₗ[B] F.affineSectionsTower.obj n :=
  (ModuleCat.sectionsEval F.affineSectionsTower n.unop).comp
    (LinearMap.pullbackKernelFst ((affineReconstructionMap α).restrictScalars B)
      (AdicCompletion.of (affineIdeal B K) (moduleSpecΓFunctor.obj H.obj)))

/-- The original stage projection with its actual bundled module endpoints. -/
abbrev affineReconstructionStageHom (n : ℕᵒᵖ) :
    ModuleCat.of B (affineReconstructionModule α) ⟶ F.affineSectionsTower.obj n :=
  ModuleCat.ofHom (X := ModuleCat.of B (affineReconstructionModule α))
    (Y := F.affineSectionsTower.obj n) (affineReconstructionStageMap α n)

/-- The actual affine maps are compatible at every original transition. -/
theorem affineReconstructionStageMap_naturality {m n : ℕᵒᵖ} (g : m ⟶ n) :
    affineReconstructionStageHom α m ≫
        moduleSpecΓFunctor.map (F.obj.map g) =
      affineReconstructionStageHom α n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact x.val.1.property g

/-- Original compatible maps from the coherent reconstruction coefficient
to every formal stage. -/
def affineReconstructionSheafStages (t : ℕ) (h : AdicSystem.DefectsKilled K t α) :
    (Functor.const ℕᵒᵖ).obj (affineReconstructionSheaf α t h).obj ⟶ F.obj where
  app n := tilde.map (affineReconstructionStageHom α n) ≫
    (F.obj.obj n).fromTildeΓ
  naturality m n g := by
    change 𝟙 _ ≫ _ = _ ≫ F.obj.map g
    have hn : tilde.map (moduleSpecΓFunctor.map (F.obj.map g)) ≫
        (F.obj.obj n).fromTildeΓ = (F.obj.obj m).fromTildeΓ ≫ F.obj.map g :=
      (fromTildeΓNatTrans (R := B)).naturality (F.obj.map g)
    rw [Category.id_comp, Category.assoc, ← hn, ← Category.assoc,
      ← tilde.map_comp, affineReconstructionStageMap_naturality]

/-- The constructed completion morphism is the canonical factor through
actual quotient units, rather than a newly chosen formal map. -/
def affineReconstructionCompletionMap (t : ℕ) (h : AdicSystem.DefectsKilled K t α) :
    (completionFunctor (Spec B) K).obj (affineReconstructionSheaf α t h) ⟶ F :=
  completionDesc K (affineReconstructionSheaf α t h) F
    (affineReconstructionSheafStages α t h)

/-- The original affine stage maps retain the defining pullback square
with the actual algebraic quotient unit. -/
theorem affineReconstructionStageMap_comp (n : ℕᵒᵖ) :
    affineReconstructionStageHom α n ≫
        moduleSpecΓFunctor.map (α.hom.app n) =
      affineReconstructionTargetHom α ≫
        moduleSpecΓFunctor.map ((idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app H.obj) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hp := LinearMap.congr_fun
    (LinearMap.pullbackKernel_comm ((affineReconstructionMap α).restrictScalars B)
      (AdicCompletion.of (affineIdeal B K) (moduleSpecΓFunctor.obj H.obj))) x
  change (affineReconstructionMapData α).map x.val.1 =
    AdicCompletion.of (affineIdeal B K) _ x.val.2 at hp
  exact NativeReconstructionData.stage_square (affineIdeal B K)
    F.affineSectionsTower ((completionFunctor (Spec B) K).obj H).affineSectionsTower
    F.affineSections_isCompatibleSystem (affineCompletionUnit B K H)
    (affineQuotientComparison B K H.obj) (AdicSystem.affineSectionsMap α)
    (affineReconstructionMapData α) x.val.1 x.val.2 hp n.unop

/-- The geometric stage square is the sheafification of the original affine
pullback square, using the actual tilde/global-section counits. -/
theorem affineReconstructionSheafStages_comp (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) (n : ℕᵒᵖ) :
    (affineReconstructionSheafStages α t h).app n ≫ α.hom.app n =
      (affineReconstructionSheafMap α t h).hom ≫
        (idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app H.obj := by
  change (tilde.map (affineReconstructionStageHom α n) ≫
    (F.obj.obj n).fromTildeΓ) ≫ α.hom.app n = _
  have hα : tilde.map (moduleSpecΓFunctor.map (α.hom.app n)) ≫
      (((completionFunctor (Spec B) K).obj H).obj.obj n).fromTildeΓ =
      (F.obj.obj n).fromTildeΓ ≫ α.hom.app n :=
    (fromTildeΓNatTrans (R := B)).naturality (α.hom.app n)
  have hu : tilde.map (moduleSpecΓFunctor.map
      ((idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app H.obj)) ≫
      (((completionFunctor (Spec B) K).obj H).obj.obj n).fromTildeΓ =
      H.obj.fromTildeΓ ≫ (idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app H.obj :=
    (fromTildeΓNatTrans (R := B)).naturality
      ((idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app H.obj)
  calc
    _ = tilde.map (affineReconstructionStageHom α n ≫
        moduleSpecΓFunctor.map (α.hom.app n)) ≫
        (((completionFunctor (Spec B) K).obj H).obj.obj n).fromTildeΓ := by
      simp only [tilde.map_comp, Category.assoc, hα]
    _ = tilde.map (affineReconstructionTargetHom α ≫
        moduleSpecΓFunctor.map ((idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app H.obj)) ≫
        (((completionFunctor (Spec B) K).obj H).obj.obj n).fromTildeΓ := by
      rw [affineReconstructionStageMap_comp]
    _ = _ := by
      rw [tilde.map_comp, Category.assoc, hu]
      rfl

/-- The original completion map is compatible with the original algebraic
projection. Once invertibility is proved, its inverse has orientation
`F → completion G`, with `α = β ≫ completion a`. -/
theorem affineReconstructionCompletionMap_comp (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) :
    affineReconstructionCompletionMap α t h ≫ α =
      (completionFunctor (Spec B) K).map (affineReconstructionSheafMap α t h) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  apply (cancel_epi ((idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app
    (affineReconstructionSheaf α t h).obj)).mp
  change (idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app _ ≫
      idealSheafQuotientDesc (Spec B) (K ^ n.unop)
        ((affineReconstructionSheafStages α t h).app n) (F.property.annihilated n.unop) ≫
      α.hom.app n =
    (idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app _ ≫
      (idealSheafQuotientFunctor (Spec B) (K ^ n.unop)).map
        (affineReconstructionSheafMap α t h).hom
  rw [← Category.assoc, idealSheafQuotientUnit_desc,
    ← (idealSheafQuotientUnit (Spec B) (K ^ n.unop)).naturality]
  exact affineReconstructionSheafStages_comp α t h n

end AlgebraicGeometry.Scheme.Modules.Coherent
