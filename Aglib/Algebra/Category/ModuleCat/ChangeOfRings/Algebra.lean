/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Native scalar extension and a specified algebra tensor product

For a specified algebra structure, the original scalar-extension object
along `algebraMap` identifies with the original algebra tensor product.
The isomorphism is native tensor congruence on the restricted regular
module. It retains every pure tensor and the original coefficient map;
ring and module universes are independent.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TensorProduct
open scoped ChangeOfRings

namespace ModuleCat

universe u v w

variable (R : Type u) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]

/-- Original scalar extension along the specified algebra map is the original algebra
tensor product, with its existing scalar actions. -/
def extendScalarsAlgebraObjIso (M : ModuleCat.{v} R) :
    (extendScalars (algebraMap R S)).obj M ≅ ModuleCat.of S (S ⊗[R] M) := by
  let A : ModuleCat R := (restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  letI : IsScalarTower R S A := {
    smul_assoc := fun r a b => by
      change (r • a) * (show S from b) = algebraMap R S r * (a * (show S from b))
      rw [Algebra.smul_def, mul_assoc] }
  let e : A ≃ₗ[S] S := LinearEquiv.refl _ _
  exact (AlgebraTensorModule.congr e (LinearEquiv.refl R M)).toModuleIso

/-- The native scalar-extension/tensor comparison retains each original pure tensor. -/
@[simp]
theorem extendScalarsAlgebraObjIso_hom_tmul (M : ModuleCat.{v} R) (s : S) (m : M) :
    (extendScalarsAlgebraObjIso R S M).hom (s ⊗ₜ[R,algebraMap R S] m) = s ⊗ₜ[R] m := rfl

/-- The inverse comparison also retains each original pure tensor. -/
@[simp]
theorem extendScalarsAlgebraObjIso_inv_tmul (M : ModuleCat.{v} R) (s : S) (m : M) :
    (extendScalarsAlgebraObjIso R S M).inv (s ⊗ₜ[R] m) =
      s ⊗ₜ[R,algebraMap R S] m := rfl

/-- Native scalar-extension maps correspond to the original algebra base-change maps. -/
@[reassoc]
theorem extendScalarsAlgebraObjIso_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (extendScalars (algebraMap R S)).map f ≫ (extendScalarsAlgebraObjIso R S N).hom =
      (extendScalarsAlgebraObjIso R S M).hom ≫ ModuleCat.ofHom (f.hom.baseChange S) := by
  apply ExtendScalars.hom_ext
  intro m
  rfl

end ModuleCat
