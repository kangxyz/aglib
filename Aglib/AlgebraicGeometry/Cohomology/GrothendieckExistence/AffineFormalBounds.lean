/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineDefectSections
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineFormalSeparation
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineReconstructionMap
public import Aglib.RingTheory.AdicCompletion.CompatibleSystemBounds

/-!
# Completed bounds supplied by actual geometric formal defects

Ordinary finite-stage sheaf bounds are transported through original affine
sections and actual compatible-family maps. Separation of the actual cokernel
is proved from finite completed scalars, not assumed as an extra geometric
hypothesis. The final bounds apply to the original map used by reconstruction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F G : AdicSystem (Spec B) K}

/-- Original geometric stage bounds give completed affine bounds, allowing
the bounding ideal to differ from the ideal defining the formal system. -/
theorem affineFormalSectionsMap_bounds (φ : F ⟶ G)
    (J : (Spec B).IdealSheafData) (t : ℕ) (h : AdicSystem.DefectsKilled J t φ) :
    let := F.affineFormalSectionsModule
    let := G.affineFormalSectionsModule
    let := F.affineSections_isCompatibleSystem.sectionsScalarTower
    let := G.affineSections_isCompatibleSystem.sectionsScalarTower
    affineIdeal B J ^ t • ((AdicSystem.affineFormalSectionsMap φ).restrictScalars B).ker = ⊥ ∧
      affineIdeal B J ^ t • (⊤ : Submodule B G.affineFormalSections) ≤
        ((AdicSystem.affineFormalSectionsMap φ).restrictScalars B).range := by
  let := F.affineFormalSectionsModule
  let := G.affineFormalSectionsModule
  let := F.affineSections_isCompatibleSystem.sectionsScalarTower
  let := G.affineSections_isCompatibleSystem.sectionsScalarTower
  let maps := fun j => ((AdicSystem.affineSectionsMap φ).app j).hom
  have compat : ∀ {j k} (a : j ⟶ k) x,
      maps k (F.affineSectionsTower.map a x) = G.affineSectionsTower.map a (maps j x) :=
    fun a x => ConcreteCategory.congr_hom ((AdicSystem.affineSectionsMap φ).naturality a) x
  let : IsHausdorff (affineIdeal B K)
      (G.affineFormalSections ⧸ (ModuleCat.sectionsMapOfLinearMaps maps compat).range) :=
    AdicSystem.affineFormalSectionsMap_cokernel_isHausdorff φ
  constructor
  · exact AdicCompletion.IsCompatibleSystem.sectionsMap_smul_ker_eq_bot maps compat
      (affineIdeal B J ^ t) (fun n => (defectsKilled_affineSections_bounds φ J t h n).1)
  · exact F.affineSections_isCompatibleSystem.sectionsMap_smul_top_le_range
      G.affineSections_isCompatibleSystem maps compat (IsNoetherian.noetherian _)
      (affineIdeal B J ^ t) (fun n => (defectsKilled_affineSections_bounds φ J t h n).2)

/-- The actual affine reconstruction map inherits both bounds from the
original ordinary sheaf defects, without additional realization data. -/
theorem affineReconstructionMap_bounds {H : (Spec B).CoherentSheaf}
    (α : F ⟶ (completionFunctor (Spec B) K).obj H)
    (J : (Spec B).IdealSheafData) (t : ℕ) (h : AdicSystem.DefectsKilled J t α) :
    let := F.affineFormalSectionsModule
    let := F.affineSections_isCompatibleSystem.sectionsScalarTower
    affineIdeal B J ^ t • ((affineReconstructionMap α).restrictScalars B).ker = ⊥ ∧
      affineIdeal B J ^ t •
        (⊤ : Submodule B (AdicCompletion (affineIdeal B K) (moduleSpecΓFunctor.obj H.obj))) ≤
          ((affineReconstructionMap α).restrictScalars B).range := by
  let := F.affineFormalSectionsModule
  let := F.affineSections_isCompatibleSystem.sectionsScalarTower
  let := ((completionFunctor (Spec B) K).obj H).affineFormalSectionsModule
  let :=
    ((completionFunctor (Spec B) K).obj H).affineSections_isCompatibleSystem.sectionsScalarTower
  let e := affineCompletionSectionsEquiv B K H
  let s := AdicSystem.affineFormalSectionsMap α
  have hs := affineFormalSectionsMap_bounds α J t h
  constructor
  · apply le_antisymm _ bot_le
    apply Submodule.smul_le.mpr
    intro a ha x hx
    change affineReconstructionMap α x = 0 at hx
    have hx' : x ∈ (s.restrictScalars B).ker := by
      apply e.symm.injective
      change affineReconstructionMap α x = e.symm 0
      simpa only [map_zero] using hx
    have hz := Submodule.smul_mem_smul ha hx'
    rw [hs.1] at hz
    exact hz
  · apply Submodule.smul_le.mpr
    intro a ha y hy
    obtain ⟨x, hx⟩ := hs.2 (Submodule.smul_mem_smul ha
      (Submodule.mem_top : e y ∈ (⊤ : Submodule B
        ((completionFunctor (Spec B) K).obj H).affineFormalSections)))
    refine ⟨x, ?_⟩
    change (e.symm.restrictScalars B) (s x) = a • y
    change s x = a • e y at hx
    rw [hx, LinearEquiv.map_smul]
    change a • e.symm (e y) = a • y
    rw [LinearEquiv.symm_apply_apply]

end AlgebraicGeometry.Scheme.Modules.Coherent
