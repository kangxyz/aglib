/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpen

/-! The original ambient mixed-open map keeps its original Ext operator and unsigned boundary. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] (X Y : FScheme k)

open CategoryTheory.Abelian

local instance : HasExt.{u + 1} (SheafOfModules.{u} X.left.ringCatSheaf) :=
  SheafOfModules.hasExt X.left.ringCatSheaf
local instance : HasExt.{u + 1} (SheafOfModules.{u} Y.left.ringCatSheaf) :=
  SheafOfModules.hasExt Y.left.ringCatSheaf
local instance : CategoryTheory.Linear k X.left.Modules :=
  Scheme.Modules.moduleCategoryLinearOfHom X.left (Scheme.constants X)
local instance : CategoryTheory.Linear k Y.left.Modules :=
  Scheme.Modules.moduleCategoryLinearOfHom Y.left (Scheme.constants Y)

example (U : Y.left.Opens) {p q n : ℕ} (h : p + q = n)
    (x : Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
      (SheafOfModules.unit X.left.ringCatSheaf) p)
    (y : Ext.{u + 1} (C := Y.left.Modules) (Scheme.Modules.openFree Y.left U)
      (SheafOfModules.unit Y.left.ringCatSheaf) q) :
    structureExternalOpenTensor X Y U h
        (structureExtLinearEquiv X p x ⊗ₜ[k] structureOpenExtLinearEquiv Y U q y) =
      moduleOpenExtCohomologyMap (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ U)
        (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n
        (structureExternalOpenExt X Y U h x y) := by
  have hCup := structureExternalOpenCup_apply X Y U h
    (structureExtLinearEquiv X p x) (structureOpenExtLinearEquiv Y U q y)
  have hTensor := structureExternalOpenTensor_tmul X Y U h
    (structureExtLinearEquiv X p x) (structureOpenExtLinearEquiv Y U q y)
  have hFinal := hTensor.trans hCup
  simp only [LinearEquiv.symm_apply_apply] at hFinal
  exact hFinal

example (U V : Y.left.Opens) {p q n : ℕ} (h : p + q = n)
    (x : Scheme.structureCohomology k X p) (y : structureOpenCohomology Y (U ⊓ V) q) :
    structureExternalOpenCup X Y (U ⊔ V) (show p + (q + 1) = n + 1 by omega) x
        (structureOpenMayerVietorisDelta Y U V q y) =
      ((-1 : ℤ) ^ p) •
        structureOpenMayerVietorisDelta (X ⊗ Y)
          ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n
          (structureExternalOpenCup X Y (U ⊓ V) h x y) :=
  structureExternalOpenCup_mayerVietoris X Y U V h x y
