/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ScalarExtensionUnit
public import Mathlib.Algebra.Category.Ring.Constructions

/-! # The canonical scalar base-change map

For a commutative square of rings the map is the original scalar-adjunction mate.
For a pushout square its invertibility follows from the native tensor cancellation
equivalence, with no flatness or finite-generation hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable {R S T P : CommRingCat.{u}}
  (i : R ⟶ S) (j : R ⟶ T) (k : S ⟶ P) (l : T ⟶ P) (h : i ≫ k = j ≫ l)

/-- The scalar base-change map is adjoint to the restricted original extension unit. -/
def scalarBaseChangeMap (M : ModuleCat.{u} S) :
    (extendScalars j.hom).obj ((restrictScalars i.hom).obj M) ⟶
      (restrictScalars l.hom).obj ((extendScalars k.hom).obj M) :=
  ((extendRestrictScalarsAdj j.hom).homEquiv _ _).symm
    (restrictedExtensionUnit i.hom k.hom (j ≫ l).hom
        (congrArg CommRingCat.Hom.hom h.symm) M ≫
      (restrictScalarsComp j.hom l.hom).hom.app ((extendScalars k.hom).obj M))

/-- The canonical scalar map retains the original extension/restriction units. -/
theorem scalarBaseChangeMap_unit (M : ModuleCat.{u} S) :
    (extendRestrictScalarsAdj j.hom).unit.app ((restrictScalars i.hom).obj M) ≫
      (restrictScalars j.hom).map (scalarBaseChangeMap i j k l h M) =
    restrictedExtensionUnit i.hom k.hom (j ≫ l).hom
        (congrArg CommRingCat.Hom.hom h.symm) M ≫
      (restrictScalarsComp j.hom l.hom).hom.app ((extendScalars k.hom).obj M) :=
  (Equiv.apply_symm_apply ((extendRestrictScalarsAdj j.hom).homEquiv _ _) _)

/-- The original scalar base-change map sends the unit pure tensor to the unit pure tensor. -/
theorem scalarBaseChangeMap_one_tmul (M : ModuleCat.{u} S) (m : M) :
    scalarBaseChangeMap i j k l h M
        ((1 : T) ⊗ₜ[R,j.hom] (m : (restrictScalars i.hom).obj M)) =
      (1 : P) ⊗ₜ[S,k.hom] m := by
  exact congrArg (fun q => q m) (scalarBaseChangeMap_unit i j k l h M)

/-- The canonical scalar base-change mate is invertible on every module over a pushout square. -/
theorem scalarBaseChangeMap_isIso_of_isPushout (hpush : IsPushout i j k l)
    (M : ModuleCat.{u} S) : IsIso (scalarBaseChangeMap i j k l hpush.w M) := by
  let : Algebra R S := i.hom.toAlgebra
  let : Algebra R T := j.hom.toAlgebra
  let : Algebra S P := k.hom.toAlgebra
  let : Algebra T P := l.hom.toAlgebra
  let : Algebra R P := (i ≫ k).hom.toAlgebra
  let : IsScalarTower R S P := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R T P := IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (fun q : R ⟶ P => q r) hpush.w
  let : Algebra.IsPushout R T S P :=
    CommRingCat.isPushout_iff_isPushout.mp hpush.flip
  let : Module R M := Module.compHom M i.hom
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : (extendScalars j.hom).obj ((restrictScalars i.hom).obj M) ≅
      (restrictScalars l.hom).obj ((extendScalars k.hom).obj M) :=
    (Algebra.IsPushout.cancelBaseChange R T S P M).symm.toModuleIso
  have he : scalarBaseChangeMap i j k l hpush.w M = e.hom := by
    apply ((extendRestrictScalarsAdj j.hom).homEquiv _ _).injective
    ext m
    change scalarBaseChangeMap i j k l hpush.w M ((1 : T) ⊗ₜ[R,j.hom] m) =
      (Algebra.IsPushout.cancelBaseChange R T S P M).symm ((1 : T) ⊗ₜ[R] m)
    rw [scalarBaseChangeMap_one_tmul, Algebra.IsPushout.cancelBaseChange_symm_tmul]
    simp only [map_one]
  rw [he]
  infer_instance

end ModuleCat
