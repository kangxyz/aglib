/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.LocalSpectrum
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-!
# Original function fields in a target-stalk pullback square

The square commutes through the original generic-stalk maps. The actual
flat-preimmersion projection identifies its function field, and cancellation
of the original local-spectrum field map preserves birationality. The
cancellation body is extracted once from RationalSingularities.RegularTarget.
No properness, Noetherianity, normality or surface premise is used here.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

private theorem originalFieldMap_congr
    {P X : Scheme.{u}} [IsIntegral P] [IsIntegral X]
    {b c : P ⟶ X} [IsDominant b] [IsDominant c] (h : b = c) :
    functionFieldMap b = functionFieldMap c := by
  subst c
  rfl

/-- The actual pullback square gives the original field-map square, without
choosing another fraction field or scalar action. -/
theorem functionFieldMap_square_of_isPullback_fromSpecStalk
    {X Y T : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral T]
    (f : Y ⟶ X) [IsDominant f] (x : X)
    (a : T ⟶ Y) [IsDominant a]
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsDominant p]
    (H : IsPullback a p f (X.fromSpecStalk x)) :
    letI := fromSpecStalk_isDominant X x
    (functionFieldMap a).comp (functionFieldMap f) =
      (functionFieldMap p).comp (functionFieldMap (X.fromSpecStalk x)) := by
  let : IsDominant (X.fromSpecStalk x) := fromSpecStalk_isDominant X x
  exact (functionFieldMap_comp a f).symm.trans
    ((originalFieldMap_congr H.w).trans (functionFieldMap_comp p (X.fromSpecStalk x)))

/-- Original birationality survives the actual local-spectrum square by
cancelling its native generic-stalk isomorphism. Dominance and integrality
are the genuine original geometric inputs, not replacement-model data. -/
theorem functionFieldMap_isIso_of_isPullback_fromSpecStalk
    {X Y T : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral T]
    (f : Y ⟶ X) [IsDominant f] (x : X)
    (a : T ⟶ Y) [IsDominant a]
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsDominant p]
    (H : IsPullback a p f (X.fromSpecStalk x))
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    IsIso (CommRingCat.ofHom (functionFieldMap p)) := by
  let s := X.fromSpecStalk x
  let : Flat s := fromSpecStalk_flat X x
  let : Flat a := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsPreimmersion a := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsDominant s := fromSpecStalk_isDominant X x
  let : IsIso (CommRingCat.ofHom (functionFieldMap a)) :=
    functionFieldMap_isIso_of_flat_preimmersion a
  let : IsIso (CommRingCat.ofHom (functionFieldMap s)) :=
    functionFieldMap_isIso_of_flat_preimmersion s
  let : IsIso (CommRingCat.ofHom (functionFieldMap f)) := hff
  have hsff : functionFieldMap (a ≫ f) = functionFieldMap (p ≫ s) :=
    originalFieldMap_congr H.w
  have hps : IsIso (CommRingCat.ofHom (functionFieldMap (p ≫ s))) := by
    rw [← hsff, functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  rw [functionFieldMap_comp, CommRingCat.ofHom_comp] at hps
  let : IsIso (CommRingCat.ofHom (functionFieldMap s) ≫
      CommRingCat.ofHom (functionFieldMap p)) := hps
  exact IsIso.of_isIso_comp_left (CommRingCat.ofHom (functionFieldMap s)) _

end AlgebraicGeometry.Scheme
