/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.MayerVietoris

/-! Native original-source consumers of the external Mayer–Vietoris sign. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules TopologicalSpace

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] (X Y : FScheme k) (U V : Y.left.Opens)

example :
    (structureExternalMayerVietorisMap X Y U V).τ₃ =
      ((structureExternalOpenSourceIso X Y).app (U ⊔ V)).inv :=
  structureExternalMayerVietorisMap_τ₃ X Y U V

example {p q n : ℕ} (h : p + q = n)
    (x : Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
      (SheafOfModules.unit X.left.ringCatSheaf) p)
    (y : Ext.{u + 1} (C := Y.left.Modules) (openFree Y.left (U ⊓ V))
      (SheafOfModules.unit Y.left.ringCatSheaf) q) :
    moduleOpenExtCohomologyMap (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ (U ⊔ V))
        (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) (n + 1)
        (structureExternalOpenExt X Y (U ⊔ V) (show p + (q + 1) = n + 1 by omega) x
          ((moduleOpenMayerVietoris_shortExact Y.left U V).extClass.comp y
            (Nat.add_comm 1 q))) =
      ((-1 : ℤ) ^ p) •
        (Opens.mayerVietorisSquare ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V)).δ
          (moduleAddSheaf (X ⊗ Y).left (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf))
          n (n + 1) rfl
          (moduleOpenExtCohomologyMap (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ (U ⊓ V))
            (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n
            (structureExternalOpenExt X Y (U ⊓ V) h x y)) :=
  structureExternalOpenExt_mayerVietoris_cohomology X Y U V h x y
