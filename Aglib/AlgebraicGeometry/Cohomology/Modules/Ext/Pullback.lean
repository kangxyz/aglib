/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Restriction
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism

/-!
# Exact module pullback and the original geometric cohomology map

The additive inverse-image comparison is the original mate of the native
module pullback unit. Its original integer generator is normalized by
the actual structural map and native pullback of the unit module. For a
flat morphism, exact module pullback on Ext therefore gives exactly the
unchanged geometric cohomology map. No quasicoherence or finiteness is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- Original additive inverse image compared with the native geometric module pullback. -/
def modulePullbackAdditiveComparison :
    SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙ zariskiPullback p ⟶
      Scheme.Modules.pullback p ⋙ SheafOfModules.toSheaf.{u} Y.ringCatSheaf where
  app M := moduleCoefficientPullback (M := M) (N := (Scheme.Modules.pullback p).obj M) p
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M)
  naturality := by
    intro M N f
    change (zariskiPullback p).map ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f) ≫
        moduleCoefficientPullback p ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N) =
      moduleCoefficientPullback p ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) ≫
        (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map ((Scheme.Modules.pullback p).map f)
    rw [← moduleCoefficientPullback_precomp p f,
      ← moduleCoefficientPullback_postcomp p _ ((Scheme.Modules.pullback p).map f)]
    apply congrArg (moduleCoefficientPullback p)
    exact (Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality f

/-- The actual module pullback unit followed by the original unit-module comparison is
precisely the original structural sheaf map. -/
theorem modulePullbackAdditiveComparison_unit :
    (modulePullbackAdditiveComparison p).app (SheafOfModules.unit X.ringCatSheaf) ≫
        (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map (Scheme.Modules.pullbackUnitIso p).hom =
      structurePullbackMap p := by
  rw [modulePullbackAdditiveComparison, ← moduleCoefficientPullback_postcomp]
  have hunit :
      (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pushforward p).map (Scheme.Modules.pullbackUnitIso p).hom =
      SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom := by
    have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      p.toRingCatSheafHom
    change (Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _
      (Scheme.Modules.pullbackUnitIso p).hom = _ at h
    simpa only [Adjunction.homEquiv_apply] using h
  rw [hunit]
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} p.base
  apply (adj.homEquiv _ _).injective
  rw [moduleCoefficientPullback_homEquiv]
  have hAdj : adj.homEquiv
      (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf))
      (moduleAddSheaf Y (SheafOfModules.unit Y.ringCatSheaf))
      (structurePullbackMap p) = structurePushforwardMap p :=
    Equiv.apply_symm_apply _ _
  rw [hAdj]
  apply CategoryTheory.Sheaf.hom_ext
  ext U x
  rfl

/-- Native pullback preserves the original integer generator through the actual structural map. -/
theorem modulePullbackAdditiveComparison_integer :
    (constantPullbackIso p).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)) ≫
        (zariskiPullback p).map (moduleUnitIntegerMap X) ≫
          (modulePullbackAdditiveComparison p).app (SheafOfModules.unit X.ringCatSheaf) =
      moduleUnitIntegerMap Y ≫
        (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map (Scheme.Modules.pullbackUnitIso p).inv := by
  apply (cancel_mono
    ((SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map (Scheme.Modules.pullbackUnitIso p).hom)).mp
  simp only [Category.assoc, modulePullbackAdditiveComparison_unit,
    moduleUnitIntegerMap_structurePullback, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

variable [Flat p]

/-- Exact module pullback computes the original geometric cohomology map with its actual unit. -/
theorem moduleExtCohomologyMap_pullback (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n) :
    moduleCohomologyMapAlong (M := M) (N := (Scheme.Modules.pullback p).obj M) p
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n
        (moduleExtCohomologyMap X M n x) =
      moduleExtCohomologyMap Y ((Scheme.Modules.pullback p).obj M) n
        ((Ext.mk₀ (Scheme.Modules.pullbackUnitIso p).inv).comp
          (x.mapExactFunctor (Scheme.Modules.pullback p)) (Nat.zero_add n)) := by
  let RJ : X.Modules ⥤ Y.Modules := Scheme.Modules.pullback p
  let : RJ.Additive := inferInstanceAs ((Scheme.Modules.pullback p).Additive)
  let : PreservesFiniteLimits RJ :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pullback p))
  let : PreservesFiniteColimits RJ :=
    inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.pullback p))
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
  let τ : SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙ zariskiPullback p ⟶ G :=
    modulePullbackAdditiveComparison p
  let fx : Ext.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf))
      (moduleAddSheaf X M) n := x.mapExactFunctor (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  let rx : Ext.{u + 1}
      (RJ.obj (SheafOfModules.unit X.ringCatSheaf)) (RJ.obj M) n :=
    x.mapExactFunctor RJ
  have hnat :
      (fx.mapExactFunctor (zariskiPullback p)).comp
        (Ext.mk₀ ((modulePullbackAdditiveComparison p).app M)) (Nat.add_zero n) =
      (Ext.mk₀ ((modulePullbackAdditiveComparison p).app
          (SheafOfModules.unit X.ringCatSheaf))).comp
        (rx.mapExactFunctor FY) (Nat.zero_add n) := by
    have h := Ext.mapExactFunctor_comp_mk₀_natTransApp x τ
    have hf : x.mapExactFunctor
          (SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙ zariskiPullback p) =
        fx.mapExactFunctor (zariskiPullback p) :=
      Ext.comp_mapExactFunctor x (SheafOfModules.toSheaf.{u} X.ringCatSheaf) (zariskiPullback p)
    have hg : x.mapExactFunctor G = rx.mapExactFunctor FY :=
      Ext.comp_mapExactFunctor x RJ FY
    rw [hf, hg] at h
    exact h
  let sourceClass := (Ext.mk₀ (moduleUnitIntegerMap X)).comp fx (Nat.zero_add n)
  let targetClass := (Ext.mk₀ (Scheme.Modules.pullbackUnitIso p).inv).comp rx (Nat.zero_add n)
  change ((Ext.mk₀ ((constantPullbackIso p).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)))).comp
      (sourceClass.mapExactFunctor (zariskiPullback p)) (Nat.zero_add n)).comp
      (Ext.mk₀ ((modulePullbackAdditiveComparison p).app M)) (Nat.add_zero n) =
    (Ext.mk₀ (moduleUnitIntegerMap Y)).comp
      (targetClass.mapExactFunctor FY) (Nat.zero_add n)
  dsimp only [sourceClass, targetClass]
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]
  rw [hnat]
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc,
    modulePullbackAdditiveComparison_integer, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero]


end AlgebraicGeometry.Scheme.Cohomology
