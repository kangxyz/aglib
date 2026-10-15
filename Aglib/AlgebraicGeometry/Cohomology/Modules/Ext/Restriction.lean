/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Composition
public import Aglib.AlgebraicGeometry.Modules.Exact

/-! # Original module Ext and geometric open restriction

The comparison from additive inverse image to the original restricted module
is the native mate of the module restriction unit. Its integer generator is
normalized by the original structure-sheaf map and actual degree-zero
geometric cohomology. No alternative restriction model is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} (j : Y ⟶ X)

/-- Original inverse image and the structure-sheaf map preserve the integer generator one. -/
theorem moduleUnitIntegerMap_structurePullback :
    (constantPullbackIso j).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)) ≫
        (zariskiPullback j).map (moduleUnitIntegerMap X) ≫ structurePullbackMap j =
      moduleUnitIntegerMap Y := by
  let A := moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)
  let B := moduleAddSheaf Y (SheafOfModules.unit Y.ringCatSheaf)
  let x : Sheaf.H.{u + 1} A 0 := Ext.mk₀ (moduleUnitIntegerMap X)
  have hx : Ext.addEquiv₀ x = moduleUnitIntegerMap X := by
    change Ext.addEquiv₀ (Ext.mk₀ (moduleUnitIntegerMap X)) = _
    rw [← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  have hAdj : (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} j.base).homEquiv
      A B (structurePullbackMap j) = structurePushforwardMap j :=
    Equiv.apply_symm_apply _ _
  have h0 := zariskiCohomologyMap_equiv₀ j A B (structurePullbackMap j) x
  change integerSheafHomEquiv B
      (Ext.addEquiv₀ (zariskiCohomologyMap j A B (structurePullbackMap j) 0 x)) =
    (pushforwardSectionsIso j).hom.app B
      (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} j.base).homEquiv
        A B (structurePullbackMap j)).hom.app (op ⊤)
          (integerSheafHomEquiv A (Ext.addEquiv₀ x))) at h0
  rw [zariskiCohomologyMap_addEquiv₀, hx, moduleUnitIntegerMap_sections, hAdj] at h0
  have h1 : (pushforwardSectionsIso j).hom.app B
      ((structurePushforwardMap j).hom.app (op ⊤) (1 : Γ(X, ⊤))) = (1 : Γ(Y, ⊤)) := by
    change (Y.presheaf.map _).hom ((j.app ⊤).hom 1) = 1
    simp only [map_one]
  apply (integerSheafHomEquiv B).injective
  rw [moduleUnitIntegerMap_sections]
  exact h0.trans h1

variable [IsOpenImmersion j]

/-- Native additive inverse image compared with original module restriction after forgetting. -/
def moduleRestrictionAdditiveComparison :
    SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙ zariskiPullback j ⟶
      Scheme.Modules.restrictFunctor j ⋙ SheafOfModules.toSheaf.{u} Y.ringCatSheaf where
  app M := moduleCoefficientPullback (M := M) (N := (Scheme.Modules.restrictFunctor j).obj M) j
    ((Scheme.Modules.restrictAdjunction j).unit.app M)
  naturality := by
    intro M N f
    change (zariskiPullback j).map ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f) ≫
        moduleCoefficientPullback j ((Scheme.Modules.restrictAdjunction j).unit.app N) =
      moduleCoefficientPullback j ((Scheme.Modules.restrictAdjunction j).unit.app M) ≫
        (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map ((Scheme.Modules.restrictFunctor j).map f)
    rw [← moduleCoefficientPullback_precomp j f,
      ← moduleCoefficientPullback_postcomp j _ ((Scheme.Modules.restrictFunctor j).map f)]
    apply congrArg (moduleCoefficientPullback j)
    exact (Scheme.Modules.restrictAdjunction j).unit.naturality f

/-- The native unit comparison on the structure module is the actual structural pullback map. -/
theorem moduleRestrictionAdditiveComparison_unit :
    (moduleRestrictionAdditiveComparison j).app (SheafOfModules.unit X.ringCatSheaf) ≫
        (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map (Scheme.Modules.restrictUnitIso j).hom =
      structurePullbackMap j := by
  rw [moduleRestrictionAdditiveComparison, ← moduleCoefficientPullback_postcomp]
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} j.base
  apply (adj.homEquiv _ _).injective
  rw [moduleCoefficientPullback_homEquiv]
  have hAdj : adj.homEquiv
      (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf))
      (moduleAddSheaf Y (SheafOfModules.unit Y.ringCatSheaf))
      (structurePullbackMap j) = structurePushforwardMap j :=
    Equiv.apply_symm_apply _ _
  rw [hAdj]
  apply CategoryTheory.Sheaf.hom_ext
  ext U x
  change (j.appIso (j ⁻¹ᵁ U.unop)).hom
    ((X.presheaf.map (homOfLE (j.image_preimage_le U.unop)).op).hom x) = j.app U.unop x
  have h : X.presheaf.map (homOfLE (j.image_preimage_le U.unop)).op ≫
      (j.appIso (j ⁻¹ᵁ U.unop)).hom = j.app U.unop := by
    apply (cancel_mono (j.appIso (j ⁻¹ᵁ U.unop)).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (j.app_appIso_inv U.unop).symm
  exact congrArg (fun k => k.hom x) h

/-- The original integer generator normalizes the additive/module restriction comparison. -/
theorem moduleRestrictionAdditiveComparison_integer :
    (constantPullbackIso j).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)) ≫
        (zariskiPullback j).map (moduleUnitIntegerMap X) ≫
          (moduleRestrictionAdditiveComparison j).app (SheafOfModules.unit X.ringCatSheaf) =
      moduleUnitIntegerMap Y ≫
        (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map (Scheme.Modules.restrictUnitIso j).inv := by
  apply (cancel_mono
    ((SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map (Scheme.Modules.restrictUnitIso j).hom)).mp
  simp only [Category.assoc, moduleRestrictionAdditiveComparison_unit,
    moduleUnitIntegerMap_structurePullback, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- Original module-linear Ext restriction computes the original geometric cohomology map. -/
theorem moduleExtCohomologyMap_restrict (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n) :
    moduleCohomologyMapAlong (M := M) (N := (Scheme.Modules.restrictFunctor j).obj M) j
        ((Scheme.Modules.restrictAdjunction j).unit.app M) n
        (moduleExtCohomologyMap X M n x) =
      moduleExtCohomologyMap Y ((Scheme.Modules.restrictFunctor j).obj M) n
        ((Ext.mk₀ (Scheme.Modules.restrictUnitIso j).inv).comp
          (x.mapExactFunctor (Scheme.Modules.restrictFunctor j)) (Nat.zero_add n)) := by
  let RJ : X.Modules ⥤ Y.Modules := Scheme.Modules.restrictFunctor j
  let : RJ.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteLimits RJ :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.restrictFunctor j))
  let : PreservesFiniteColimits RJ :=
    inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.restrictFunctor j))
  let FY : Y.Modules ⥤ Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} Y.ringCatSheaf
  let : FY.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteLimits FY :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} Y.ringCatSheaf))
  let : PreservesFiniteColimits FY :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} Y.ringCatSheaf))
  let G : X.Modules ⥤ Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
    RJ ⋙ FY
  let : G.Additive := inferInstance
  let : PreservesFiniteLimits G :=
    comp_preservesFiniteLimits RJ FY
  let : PreservesFiniteColimits G :=
    comp_preservesFiniteColimits RJ FY
  let τ : SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙ zariskiPullback j ⟶ G :=
    moduleRestrictionAdditiveComparison j
  let fx : Ext.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf))
      (moduleAddSheaf X M) n := x.mapExactFunctor (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  let rx : Ext.{u + 1}
      (RJ.obj (SheafOfModules.unit X.ringCatSheaf)) (RJ.obj M) n :=
    x.mapExactFunctor RJ
  have hnat :
      (fx.mapExactFunctor (zariskiPullback j)).comp
        (Ext.mk₀ ((moduleRestrictionAdditiveComparison j).app M)) (Nat.add_zero n) =
      (Ext.mk₀ ((moduleRestrictionAdditiveComparison j).app
          (SheafOfModules.unit X.ringCatSheaf))).comp
        (rx.mapExactFunctor FY) (Nat.zero_add n) := by
    have h := Ext.mapExactFunctor_comp_mk₀_natTransApp x τ
    have hf : x.mapExactFunctor
          (SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙ zariskiPullback j) =
        fx.mapExactFunctor (zariskiPullback j) :=
      Ext.comp_mapExactFunctor x (SheafOfModules.toSheaf.{u} X.ringCatSheaf) (zariskiPullback j)
    have hg : x.mapExactFunctor G = rx.mapExactFunctor FY :=
      Ext.comp_mapExactFunctor x RJ FY
    rw [hf, hg] at h
    exact h
  let sourceClass := (Ext.mk₀ (moduleUnitIntegerMap X)).comp fx (Nat.zero_add n)
  let targetClass := (Ext.mk₀ (Scheme.Modules.restrictUnitIso j).inv).comp rx (Nat.zero_add n)
  change ((Ext.mk₀ ((constantPullbackIso j).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)))).comp
      (sourceClass.mapExactFunctor (zariskiPullback j)) (Nat.zero_add n)).comp
      (Ext.mk₀ ((moduleRestrictionAdditiveComparison j).app M)) (Nat.add_zero n) =
    (Ext.mk₀ (moduleUnitIntegerMap Y)).comp
      (targetClass.mapExactFunctor FY) (Nat.zero_add n)
  dsimp only [sourceClass, targetClass]
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]
  rw [hnat]
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc,
    moduleRestrictionAdditiveComparison_integer, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero]

end AlgebraicGeometry.Scheme.Cohomology
