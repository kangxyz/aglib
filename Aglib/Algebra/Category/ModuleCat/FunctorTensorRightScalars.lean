/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.FunctorTensorScalars

/-! # The original tensor as a functor with right-factor scalars

The tensor carrier is the original `V ⊗[R] M`. Its coefficient action is the
existing right-factor action. Morphisms are the original tensor maps, not a
transported cohomology construction. No ring map from `R` to the coefficient
ring is required: the two actions on the given module commute.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

universe r l v w

variable (R : Type r) [CommRing R] (Λ : Type l) [Ring Λ]
  (M : Type v) [AddCommGroup M] [Module R M] [Module Λ M] [SMulCommClass Λ R M]

/-- The coefficient-ring action on the right tensor factor. -/
local instance tensorRightScalarsCarrierModule (V : ModuleCat.{w} R) :
    Module Λ (V ⊗[R] M) :=
  TensorProduct.rightModule R Λ V M

/-- The original tensor with the actual coefficient action on its right factor. -/
abbrev tensorRightScalarsObj (V : ModuleCat.{w} R) : ModuleCat.{max w v} Λ :=
  ModuleCat.of Λ (V ⊗[R] M)

/-- The original first-factor tensor map is linear for the right-factor action. -/
def tensorRightScalarsMap {V W : ModuleCat.{w} R} (f : V ⟶ W) :
    tensorRightScalarsObj R Λ M V ⟶ tensorRightScalarsObj R Λ M W :=
  ModuleCat.ofHom
    { (TensorProduct.map f.hom (LinearMap.id : M →ₗ[R] M)).toAddMonoidHom with
      map_smul' := by
        intro a z
        induction z using TensorProduct.inductionOn with
        | tmul x m =>
            change TensorProduct.map f.hom LinearMap.id (a • (x ⊗ₜ[R] m)) =
              a • TensorProduct.map f.hom LinearMap.id (x ⊗ₜ[R] m)
            rw [TensorProduct.rightModule_smul_tmul,
              TensorProduct.map_tmul, TensorProduct.map_tmul,
              TensorProduct.rightModule_smul_tmul]
            rfl
        | add z t hz ht =>
            change TensorProduct.map f.hom LinearMap.id (a • (z + t)) =
              a • TensorProduct.map f.hom LinearMap.id (z + t)
            change TensorProduct.map f.hom LinearMap.id (a • z) =
              a • TensorProduct.map f.hom LinearMap.id z at hz
            change TensorProduct.map f.hom LinearMap.id (a • t) =
              a • TensorProduct.map f.hom LinearMap.id t at ht
            simp only [smul_add, map_add, hz, ht] }

/-- The coefficient-linear map retains the original tensor-map function. -/
@[simp]
theorem tensorRightScalarsMap_apply {V W : ModuleCat.{w} R} (f : V ⟶ W)
    (z : V ⊗[R] M) :
    tensorRightScalarsMap R Λ M f z = TensorProduct.map f.hom LinearMap.id z := rfl

/-- Tensoring with the given bimodule uses one original tensor object and map. -/
def tensorRightScalarsFunctor : ModuleCat.{w} R ⥤ ModuleCat.{max w v} Λ where
  obj := tensorRightScalarsObj R Λ M
  map := tensorRightScalarsMap R Λ M
  map_id V := by
    ext z
    change TensorProduct.map LinearMap.id LinearMap.id z = z
    rw [TensorProduct.map_id]
    rfl
  map_comp f g := by
    ext z
    change TensorProduct.map (g.hom.comp f.hom) LinearMap.id z =
      TensorProduct.map g.hom LinearMap.id (TensorProduct.map f.hom LinearMap.id z)
    rw [TensorProduct.map_map]
    rfl

/-- The functor remains additive for the original tensor maps. -/
instance tensorRightScalarsFunctor_additive : (tensorRightScalarsFunctor R Λ M).Additive where
  map_add := by
    intro V W f g
    ext z
    change TensorProduct.map (f.hom + g.hom) LinearMap.id z =
      TensorProduct.map f.hom LinearMap.id z + TensorProduct.map g.hom LinearMap.id z
    induction z using TensorProduct.inductionOn with
    | tmul x m =>
        change (f x + g x) ⊗ₜ[R] m = f x ⊗ₜ[R] m + g x ⊗ₜ[R] m
        exact TensorProduct.add_tmul _ _ _
    | add z t hz ht =>
        simp only [map_add] at hz ht ⊢
        rw [hz, ht]
        abel

end ModuleCat
