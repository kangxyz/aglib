/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections
public import Aglib.AlgebraicGeometry.Modules.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Structural linearity of the original module tensor functor

The actual sheafified tensor respects the original global scalar center.
The proof checks the original pure-tensor section generators and the
original sheafification unit. Consequently tensoring by any module sheaf
is linear for every specified structural ring action, without a flatness,
quasicoherence or finiteness condition on either tensor factor.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry Opposite
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- The original tensor-section generator is linear in its second input for the actual
local ring action, through the original module-sheafification unit. -/
theorem moduleTensorSection_smul_right (E M : X.Modules) (U : X.Opens)
    (e : Γ(E, U)) (m : Γ(M, U)) (a : Γ(X, U)) :
    moduleTensorSection X E M U e (a • m) = a • moduleTensorSection X E M U e m := by
  let η := (SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
    (((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj E) ⊗
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M))
  change η.app (op U) (e ⊗ₜ[Γ(X, U)] (a • m)) =
    a • η.app (op U) (e ⊗ₜ[Γ(X, U)] m)
  rw [TensorProduct.tmul_smul, (η.app (op U)).hom.map_smul]

/-- Tensoring the original scalar endomorphism gives the same original scalar
endomorphism of the actual tensor sheaf. -/
theorem moduleTensorLeftFunctor_map_globalScalarEndomorphism
    (E M : X.Modules) (a : Γ(X, ⊤)) :
    (moduleTensorLeftFunctor X E).map (globalScalarEndomorphism X M a) =
      globalScalarEndomorphism X ((moduleTensorLeftFunctor X E).obj M) a := by
  apply moduleTensor_hom_ext
  intro U e m
  change ((moduleTensorLeftFunctor X E).map (globalScalarEndomorphism X M a)).val.app
      (op U) (moduleTensorSection X E M U e m) =
    (globalScalarEndomorphism X ((moduleTensorLeftFunctor X E).obj M) a).val.app
      (op U) (moduleTensorSection X E M U e m)
  erw [moduleTensorLeftFunctor_map_section, globalScalarEndomorphism_app,
    globalScalarEndomorphism_app, moduleTensorSection_smul_right]

variable {R : Type v} [CommRing R] (α : R →+* Γ(X, ⊤))

/-- Tensoring by an arbitrary module sheaf is linear for the original structural category
associated to the specified ring map. -/
instance moduleTensorLeftFunctor_linearOfHom (E : X.Modules) :
    letI := moduleCategoryLinearOfHom X α
    Functor.Linear R (moduleTensorLeftFunctor X E) := by
  let := moduleCategoryLinearOfHom X α
  apply (Functor.linear_iff R (moduleTensorLeftFunctor X E)).mpr
  intro M r
  rw [moduleCategoryLinearOfHom_smul_id, moduleCategoryLinearOfHom_smul_id]
  exact moduleTensorLeftFunctor_map_globalScalarEndomorphism X E M (α r)

/-- The actual coefficient map, with the specified original structural scalar action,
commutes with scalar multiplication on every original module morphism. -/
theorem moduleTensorLeftFunctor_map_smul (E : X.Modules) {M N : X.Modules}
    (f : M ⟶ N) (r : R) :
    letI := moduleCategoryLinearOfHom X α
    (moduleTensorLeftFunctor X E).map (r • f) =
      r • (moduleTensorLeftFunctor X E).map f := by
  let := moduleCategoryLinearOfHom X α
  exact Functor.map_smul (moduleTensorLeftFunctor X E) r f

end AlgebraicGeometry.Scheme.Modules
