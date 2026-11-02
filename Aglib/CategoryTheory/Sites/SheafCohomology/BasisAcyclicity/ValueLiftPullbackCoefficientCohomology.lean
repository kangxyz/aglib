/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLiftPullbackCohomology
public import Aglib.Algebra.Homology.DerivedCategory.Ext.CompositeComparison

/-! # Whole original value-lift pullback with coefficient postcomposition

The coefficient arrow is retained through the native exact-functor Ext law.
This completes the generic square before any geometric coefficient is supplied.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.BasisAcyclicity

open Hypercohomology

universe c h d k v t e₁ e₂ e₃ e₄

variable {C : Type c} [Category.{h} C] {D : Type d} [Category.{k} D]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{max h k v}]
  [HasSheafify K AddCommGrpCat.{max h k v}]
  [HasSheafify J AddCommGrpCat.{max h k v t}]
  [HasSheafify K AddCommGrpCat.{max h k v t}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h k v} J K).IsRightAdjoint]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h k v t} J K).IsRightAdjoint]
  [(G.sheafPullback AddCommGrpCat.{max h k v} J K).Additive]
  [(G.sheafPullback AddCommGrpCat.{max h k v t} J K).Additive]
  [PreservesFiniteLimits (G.sheafPullback AddCommGrpCat.{max h k v} J K)]
  [PreservesFiniteLimits (G.sheafPullback AddCommGrpCat.{max h k v t} J K)]
  [PreservesFiniteColimits (G.sheafPullback AddCommGrpCat.{max h k v} J K)]
  [PreservesFiniteColimits (G.sheafPullback AddCommGrpCat.{max h k v t} J K)]
  [PreservesFiniteColimits (valueLift.{c, h, max h k v, t} J)]
  [PreservesFiniteColimits (valueLift.{d, k, max h k v, t} K)]
  [HasExt.{e₁} (Sheaf J AddCommGrpCat.{max h k v})]
  [HasExt.{e₂} (Sheaf J AddCommGrpCat.{max h k v t})]
  [HasExt.{e₃} (Sheaf K AddCommGrpCat.{max h k v})]
  [HasExt.{e₄} (Sheaf K AddCommGrpCat.{max h k v t})]
  (U : C) (hU : IsTerminal U) (hGU : IsTerminal (G.obj U))

/-- The whole value-lift square includes an arbitrary original coefficient
arrow after geometric pullback. All four Ext universes remain independent. -/
theorem valueLiftPullbackMap_cohomology_comp
    (F : Sheaf J AddCommGrpCat.{max h k v})
    (H : Sheaf K AddCommGrpCat.{max h k v})
    (g : (G.sheafPullback AddCommGrpCat.{max h k v} J K).obj F ⟶ H)
    (n : ℕ) (x : Sheaf.H.{e₁} F n) :
    (valueLift.{d, k, max h k v, t} K).extPrecompMap
      (valueLiftConstantMap.{d, k, max h k v, t} hGU) H n
      (((G.sheafPullback AddCommGrpCat.{max h k v} J K).extPrecompMap
        (pullbackConstantIntegerIso.{c, h, d, k, v} G J K U hU hGU).inv F n x).comp
          (Ext.mk₀ g) (Nat.add_zero n)) =
    ((G.sheafPullback AddCommGrpCat.{max h k v t} J K).extPrecompMap
      (pullbackConstantIntegerIso.{c, h, d, k, max v t} G J K U hU hGU).inv _ n
      ((valueLift.{c, h, max h k v, t} J).extPrecompMap
        (valueLiftConstantMap.{c, h, max h k v, t} hU) F n x)).comp
      (Ext.mk₀ ((valueLiftPullbackMap.{c, h, d, k, max h k v, t} G J K).app F ≫
        (valueLift.{d, k, max h k v, t} K).map g)) (Nat.add_zero n) := by
  rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀]
  have hv := valueLiftPullbackMap_cohomology.{c, h, d, k, v, t, e₁, e₂, e₃, e₄}
    G J K U hU hGU F n x
  rw [← hv]
  change (Ext.comp _
    (Ext.mk₀ ((valueLiftPullbackMap.{c, h, d, k, max h k v, t} G J K).app F))
      (Nat.add_zero n)).comp
        (Ext.mk₀ ((valueLift.{d, k, max h k v, t} K).map g)) (Nat.add_zero n) = _
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

end CategoryTheory.Sheaf.BasisAcyclicity
