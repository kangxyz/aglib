/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Actual unit-module comparisons under open restriction

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FlatIdealBaseChange.lean`, SHA-256
  `52ad81197b39689c02c7f936d7b8987c9dac2695568d56796cdb1c43743a6864`.

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
open AlgebraicGeometry.Scheme.Modules
open LinearMap

section
namespace AlgebraicGeometry.Scheme.Modules

variable {D X Y : Scheme.{u}}

@[simp]
theorem restrictUnitIso_ι_hom_app_apply (U : X.Opens) (V : U.toScheme.Opens)
    (r : Γ(X, U.ι ''ᵁ V)) :
    ((Scheme.Modules.restrictUnitIso U.ι).hom.app V) r = r := by
  change (U.ι.appIso V).hom r = r
  rw [Scheme.Opens.ι_appIso]
  rfl

theorem restrictUnitIso_hom_adjoint (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictAdjunction f).homEquiv _ _
      (Scheme.Modules.restrictUnitIso f).hom = SheafOfModules.unitToPushforwardObjUnit
        f.toRingCatSheafHom := by
  rw [Adjunction.homEquiv_unit]
  apply Scheme.Modules.hom_ext
  intro V
  ext r
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app, ConcreteCategory.comp_apply]
  change (f.appIso (f ⁻¹ᵁ V)).hom
    (Y.presheaf.map (homOfLE (f.image_preimage_le V)).op r) = f.app V r
  erw [← f.app_appIso_inv]
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

@[reassoc]
theorem restrictFunctorIsoPullback_hom_unit (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom =
        (Scheme.Modules.restrictUnitIso f).hom := by
  apply ((Scheme.Modules.restrictAdjunction f).homEquiv _ _).injective
  change (Scheme.Modules.restrictAdjunction f).homEquiv _ _
    (((Scheme.Modules.restrictAdjunction f).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f)).hom.app _ ≫ _) = _
  have huniq :
      (Scheme.Modules.restrictAdjunction f).homEquiv _ _
        (((Scheme.Modules.restrictAdjunction f).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction f)).hom.app _ ≫
            SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := by
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
      Adjunction.homEquiv_unit]
  exact huniq.trans
    ((SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom).trans (restrictUnitIso_hom_adjoint f).symm)

@[reassoc]
theorem restrictFunctorIsoPullback_inv_unit (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).inv.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.restrictUnitIso f).hom =
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  rw [← restrictFunctorIsoPullback_hom_unit, ← Category.assoc]
  simp

end AlgebraicGeometry.Scheme.Modules
end
