/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Henselian.Arithmetic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Henselian.Geometric

/-!
# Henselian base change of proper arithmetic models with two affine opens

The actual affine binary cover pulls back to every selected local
henselization. The proved geometric local Picard theorem discharges each
selected-stage premise of the marked residue-field limit reduction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Invertible

open Algebra.FiniteTypeSubalgebraLimit LocalRing.AtLocalTarget

universe u v

/-- Every actual residue-fibre line bundle lifts after arbitrary henselian
base change of a proper finite-type arithmetic model with an affine binary cover. -/
theorem exists_lineBundle_lift_affineBinary_geometricBaseChange
    (D : Type v) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [CharZero D]
    (B R : Type u) [CommRing B] [CommRing R] [Algebra D B] [Algebra.FiniteType D B]
    [Algebra B R] [HenselianLocalRing R] {X : Scheme.{u}}
    (A : Scheme.AffineBinaryCover X) (f : X ⟶ Spec (.of B)) [IsProper f]
    (L : LineBundle (Limits.pullback
      (Limits.pullback.snd f (Spec.algebraMap B R)) (LocalRing.residueSpecMap R))) :
    ∃ W : LineBundle (Limits.pullback f (Spec.algebraMap B R)),
      Nonempty ((pullback (Limits.pullback.fst
        (Limits.pullback.snd f (Spec.algebraMap B R)) (LocalRing.residueSpecMap R))).obj W.val ≅
          L.val) := by
  apply exists_lineBundle_lift_of_residueStage_lifts B R f ?_ L
  intro s
  let S := stage B R s
  let a : S →+* R := (stage B R s).val.toRingHom
  let b : B →+* S := algebraMap B S
  let : Algebra D S := (b.comp (algebraMap D B)).toAlgebra
  let : IsScalarTower D B S := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FiniteType D S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType D B) (inferInstance : Algebra.FiniteType B S)
  let q := Localization.AtLocalTarget.prime a
  let g := Limits.pullback.snd f (henselizationSpecMap a b)
  let : IsProper g := inferInstanceAs
    (IsProper (Limits.pullback.snd f (henselizationSpecMap a b)))
  have : IsAffineHom (Limits.pullback.fst f (henselizationSpecMap a b)) :=
    MorphismProperty.pullback_fst _ _
      (inferInstance : IsAffineHom (henselizationSpecMap a b))
  let A' := A.pullback (Limits.pullback.fst f (henselizationSpecMap a b))
  exact pullbackClass_residue_affineBinary_geometricLocal_of_charZeroDVR_surjective
    D S q A' g

end AlgebraicGeometry.Scheme.Modules.Invertible
