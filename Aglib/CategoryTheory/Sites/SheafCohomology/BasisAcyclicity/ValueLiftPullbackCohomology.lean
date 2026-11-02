/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLiftPullbackSource
public import Aglib.Algebra.Homology.DerivedCategory.Ext.CompositeComparison

/-! # Original cohomology under the value-lift pullback mate

The whole square follows from the actual native mate and its proved original
constant-source equation. All four Ext universes are independent. This is an
equality of original exact-functor Ext maps, not a replacement cohomology model.
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

/-- Value lift and geometric pullback commute on the original Ext classes
through the constructed mate, with their original constant-integer maps. -/
theorem valueLiftPullbackMap_cohomology
    (F : Sheaf J AddCommGrpCat.{max h k v}) (n : ℕ) (x : Sheaf.H.{e₁} F n) :
    Sheaf.H.map ((valueLiftPullbackMap.{c, h, d, k, max h k v, t} G J K).app F) n
      ((G.sheafPullback AddCommGrpCat.{max h k v t} J K).extPrecompMap
        (pullbackConstantIntegerIso.{c, h, d, k, max v t} G J K U hU hGU).inv _ n
        ((valueLift.{c, h, max h k v, t} J).extPrecompMap
          (valueLiftConstantMap.{c, h, max h k v, t} hU) F n x)) =
    (valueLift.{d, k, max h k v, t} K).extPrecompMap
      (valueLiftConstantMap.{d, k, max h k v, t} hGU) _ n
      ((G.sheafPullback AddCommGrpCat.{max h k v} J K).extPrecompMap
        (pullbackConstantIntegerIso.{c, h, d, k, v} G J K U hU hGU).inv F n x) := by
  let L := G.sheafPullback AddCommGrpCat.{max h k v} J K
  let L' := G.sheafPullback AddCommGrpCat.{max h k v t} J K
  let V := valueLift.{c, h, max h k v, t} J
  let W := valueLift.{d, k, max h k v, t} K
  let q := pullbackConstantIntegerIso.{c, h, d, k, v} G J K U hU hGU
  let q' := pullbackConstantIntegerIso.{c, h, d, k, max v t} G J K U hU hGU
  let a := valueLiftConstantMap.{c, h, max h k v, t} (J := J) hU
  let b := valueLiftConstantMap.{d, k, max h k v, t} (J := K) hGU
  let τ := valueLiftPullbackMap.{c, h, d, k, max h k v, t} G J K
  have hs : q'.inv ≫ L'.map a ≫ τ.app _ = b ≫ W.map q.inv := by
    apply (cancel_mono (W.map q.hom)).mp
    simp only [Category.assoc]
    rw [valueLiftPullbackMap_constant]
    change q'.inv ≫ q'.hom ≫ b = b ≫ W.map q.inv ≫ W.map q.hom
    rw [q'.inv_hom_id_assoc, ← W.map_comp, q.inv_hom_id, W.map_id]
    exact (Category.comp_id b).symm
  change (L'.extPrecompMap q'.inv _ n (V.extPrecompMap a F n x)).comp
      (Ext.mk₀ (τ.app F)) (Nat.add_zero n) =
    W.extPrecompMap b _ n (L.extPrecompMap q.inv F n x)
  rw [← V.extPrecompMap_compFunctor L' a q'.inv F n x,
    ← L.extPrecompMap_compFunctor W q.inv b F n x]
  simp only [Functor.extPrecompMap_apply]
  rw [Ext.comp_assoc_of_third_deg_zero,
    Ext.mapExactFunctor_comp_mk₀_natTransApp,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  rw [Category.assoc, hs]

end CategoryTheory.Sheaf.BasisAcyclicity
