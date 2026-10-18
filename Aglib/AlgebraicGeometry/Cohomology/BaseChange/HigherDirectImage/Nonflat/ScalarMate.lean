/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Scalar mates transferred to native section modules

Linear equivalences may compare modules in different universes. Transfer the
semilinear arrow first, and take its scalar-adjunction mate in the small module
category. The tensor formula identifies this mate with the unchanged large
mate, without applying an associated-sheaf functor to a large module.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

variable {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
  {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
  {P : ModuleCat.{u + 1} R} {Q : ModuleCat.{u + 1} S}
  (e : M ≃ₗ[R] P) (d : N ≃ₗ[S] Q)
  (k : P ⟶ (ModuleCat.restrictScalars σ).obj Q)

/-- Transfer the original semilinear arrow across actual linear equivalences. -/
def smallRestrictionMap : M ⟶ (ModuleCat.restrictScalars σ).obj N :=
  ModuleCat.semilinearMapAddEquiv σ M N
    ((d.symm.toLinearMap.comp ((ModuleCat.semilinearMapAddEquiv σ P Q).symm k)).comp
      e.toLinearMap)

/-- The native scalar-adjunction mate on the small modules. -/
def smallTensorMap : (ModuleCat.extendScalars σ).obj M ⟶ N :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} σ).homEquiv _ _).symm
    (smallRestrictionMap σ e d k)

/-- The transferred mate retains the actual scalar-adjunction unit. -/
theorem smallTensorMap_unit :
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} σ).unit.app M ≫
      (ModuleCat.restrictScalars σ).map (smallTensorMap σ e d k) =
        smallRestrictionMap σ e d k :=
  Equiv.apply_symm_apply ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} σ).homEquiv _ _) _

/-- On a unit pure tensor the transferred map is the original semilinear arrow. -/
theorem smallTensorMap_one_tmul (x : M) :
    d (smallTensorMap σ e d k ((1 : S) ⊗ₜ[R,σ] x)) = k (e x) := by
  have h := congrArg (fun t => t x) (smallTensorMap_unit σ e d k)
  change smallTensorMap σ e d k ((1 : S) ⊗ₜ[R,σ] x) = d.symm (k (e x)) at h
  rw [h, LinearEquiv.apply_symm_apply]

/-- The small mate is exactly the original large mate under scalar-extended linear
equivalences. This equation crosses universes only through unbundled linear maps. -/
theorem smallTensorMap_conjugate :
    let := σ.toAlgebra
    (smallTensorMap σ e d k).hom =
      d.symm.toLinearMap.comp
        ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).homEquiv _ _).symm k).hom.comp
          (e.baseChange R S _ _).toLinearMap) := by
  let := σ.toAlgebra
  apply ModuleCat.hom_ext_iff.mp
  change smallTensorMap σ e d k = ModuleCat.ofHom _
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  apply d.injective
  rw [smallTensorMap_one_tmul]
  change k (e x) = d (d.symm
    (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).homEquiv _ _).symm k
      ((1 : S) ⊗ₜ[R,σ] e x)))
  rw [LinearEquiv.apply_symm_apply]
  exact (congrArg (fun t => t (e x))
    (Equiv.apply_symm_apply
      ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).homEquiv _ _) k)).symm

/-- Invertibility of the native small mate is exactly invertibility of the original mate. -/
theorem smallTensorMap_isIso_iff :
    IsIso (smallTensorMap σ e d k) ↔
      IsIso (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).homEquiv _ _).symm k) := by
  let := σ.toAlgebra
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  have h := smallTensorMap_conjugate σ e d k
  have hf : (smallTensorMap σ e d k : (ModuleCat.extendScalars σ).obj M → N) =
      d.symm ∘ (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).homEquiv _ _).symm k) ∘
        (e.baseChange R S _ _) := by
    funext x
    exact DFunLike.congr_fun h x
  rw [hf, Function.Bijective.of_comp_iff' d.symm.bijective,
    Function.Bijective.of_comp_iff _ (e.baseChange R S _ _).bijective]

/-- Surjectivity of the native small mate is exactly surjectivity of the original mate. -/
theorem smallTensorMap_epi_iff :
    Epi (smallTensorMap σ e d k) ↔
      Epi (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).homEquiv _ _).symm k) := by
  let := σ.toAlgebra
  rw [ModuleCat.epi_iff_surjective, ModuleCat.epi_iff_surjective]
  have h := smallTensorMap_conjugate σ e d k
  have hf : (smallTensorMap σ e d k : (ModuleCat.extendScalars σ).obj M → N) =
      d.symm ∘ (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).homEquiv _ _).symm k) ∘
        (e.baseChange R S _ _) := by
    funext x
    exact DFunLike.congr_fun h x
  rw [hf, Function.Surjective.of_comp_iff' d.symm.bijective,
    Function.Surjective.of_comp_iff _ (e.baseChange R S _ _).surjective]

end AlgebraicGeometry.Scheme.Modules.Nonflat
