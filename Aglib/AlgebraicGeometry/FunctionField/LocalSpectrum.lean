/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.FlatPreimmersion

/-!
# The original function-field comparison of a local spectrum

The actual map `X.fromSpecStalk x` is dominant and identifies the two original
generic stalks. Its function-field map commutes with the native action of
`X.presheaf.stalk x`; the resulting algebra equivalence uses that same map.
No fraction-field replacement or choice of a basis is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- This is the canonical local-spectrum morphism, not a chosen field map. -/
theorem fromSpecStalk_isDominant (X : Scheme.{u}) [IsIntegral X] (x : X) :
    IsDominant (X.fromSpecStalk x) := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff,
    ← (genericPoint_spec X).def]
  apply closure_mono
  rw [Set.singleton_subset_iff, Scheme.range_fromSpecStalk]
  exact (genericPoint_spec X).specializes trivial

local instance (X : Scheme.{u}) [IsIntegral X] (x : X) :
    IsDominant (X.fromSpecStalk x) := fromSpecStalk_isDominant X x

/-- The field map of the original local-spectrum morphism is invertible. -/
theorem fromSpecStalk_functionFieldMap_isIso (X : Scheme.{u}) [IsIntegral X] (x : X) :
    IsIso (CommRingCat.ofHom (functionFieldMap (X.fromSpecStalk x))) := by
  let : Flat (X.fromSpecStalk x) := fromSpecStalk_flat X x
  exact functionFieldMap_isIso_of_flat_preimmersion (X.fromSpecStalk x)

/-- The two native stalk scalar actions commute with the original field map. -/
theorem fromSpecStalk_functionFieldMap_comp_algebraMap
    (X : Scheme.{u}) [IsIntegral X] (x : X) :
    (functionFieldMap (X.fromSpecStalk x)).comp
        (algebraMap (X.presheaf.stalk x) X.functionField) =
      algebraMap (X.presheaf.stalk x) (Spec (X.presheaf.stalk x)).functionField := by
  suffices h : CommRingCat.ofHom
      ((functionFieldMap (X.fromSpecStalk x)).comp
        (algebraMap (X.presheaf.stalk x) X.functionField)) =
      CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) (Spec (X.presheaf.stalk x)).functionField) by
    exact congrArg CommRingCat.Hom.hom h
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk x)).1
  change Spec.map (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial) ≫
        CommRingCat.ofHom (functionFieldMap (X.fromSpecStalk x))) ≫
      X.fromSpecStalk x =
    Spec.map (StructureSheaf.toStalk (X.presheaf.stalk x) _) ≫ X.fromSpecStalk x
  rw [Spec.map_comp, Category.assoc, SpecMap_stalkSpecializes_fromSpecStalk,
    ← fromSpecStalk_genericPoint_naturality, Spec.fromSpecStalk_eq']

/-- The native local-spectrum field equivalence, over the original stalk ring. -/
def fromSpecStalkFunctionFieldAlgEquiv (X : Scheme.{u}) [IsIntegral X] (x : X) :
    X.functionField ≃ₐ[X.presheaf.stalk x] (Spec (X.presheaf.stalk x)).functionField := by
  let : IsIso (CommRingCat.ofHom (functionFieldMap (X.fromSpecStalk x))) :=
    fromSpecStalk_functionFieldMap_isIso X x
  exact
    { (asIso (CommRingCat.ofHom
        (functionFieldMap (X.fromSpecStalk x)))).commRingCatIsoToRingEquiv with
      commutes' r := DFunLike.congr_fun
        (fromSpecStalk_functionFieldMap_comp_algebraMap X x) r }

/-- The forward equivalence is the original generic-stalk map, literally. -/
theorem fromSpecStalkFunctionFieldAlgEquiv_apply
    (X : Scheme.{u}) [IsIntegral X] (x : X) (a : X.functionField) :
    fromSpecStalkFunctionFieldAlgEquiv X x a = functionFieldMap (X.fromSpecStalk x) a := rfl

end AlgebraicGeometry.Scheme
