/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.FunctorTensor

/-! # Naturality of the original tensor comparison in the module functor

A natural transformation of additive linear module functors commutes with the
canonical tensor comparison through its actual component on the lifted unit.
The proof is naturality at the original coefficient map. When both functors
preserve the coproduct indexed by a supplied basis, the same equation gives
naturality of the existing tensor equivalences and their inverses. The basis
may be infinite; ring, source-value and target-value universes remain explicit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Module
open scoped TensorProduct

namespace ModuleCat

universe r v w i

variable {R : Type r} [CommRing R]
  {F G : ModuleCat.{max r v} R ⥤ ModuleCat.{w} R}
  [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]

/-- The original tensor comparison commutes with every actual natural
transformation, using its original component on the lifted rank-one module. -/
theorem functorTensorComparison_natTrans (τ : F ⟶ G) (M : ModuleCat.{max r v} R) :
    (τ.app M).hom.comp (functorTensorComparison F M) =
      (functorTensorComparison G M).comp
        (TensorProduct.map (τ.app (liftedUnit.{r, v} R)).hom LinearMap.id) := by
  apply TensorProduct.ext'
  intro x m
  change τ.app M (F.map (coefficientHom m) x) =
    G.map (coefficientHom m) (τ.app (liftedUnit.{r, v} R) x)
  exact ConcreteCategory.congr_hom (τ.naturality (coefficientHom m)) x

/-- Evaluation of the same naturality square on any original tensor. -/
theorem functorTensorComparison_natTrans_apply (τ : F ⟶ G)
    (M : ModuleCat.{max r v} R) (z : F.obj (liftedUnit.{r, v} R) ⊗[R] M) :
    τ.app M (functorTensorComparison F M z) =
      functorTensorComparison G M
        (TensorProduct.map (τ.app (liftedUnit.{r, v} R)).hom LinearMap.id z) :=
  congrArg (fun f => f z) (functorTensorComparison_natTrans τ M)

section Basis

variable {ι : Type i} {M : ModuleCat.{max r v} R} (b : Basis ι R M)
  [PreservesColimitsOfShape (Discrete ι) F]
  [PreservesColimitsOfShape (Discrete ι) G]

/-- The basis proves invertibility without changing the forward naturality
square of the canonical tensor comparison. -/
theorem functorTensorEquivOfBasis_natTrans (τ : F ⟶ G) :
    (τ.app M).hom.comp (functorTensorEquivOfBasis F b).toLinearMap =
      (functorTensorEquivOfBasis G b).toLinearMap.comp
        (TensorProduct.map (τ.app (liftedUnit.{r, v} R)).hom LinearMap.id) :=
  functorTensorComparison_natTrans τ M

/-- The inverses of the same canonical tensor equivalences commute with the
actual natural-transformation components, including the original unit map. -/
theorem functorTensorEquivOfBasis_symm_natTrans (τ : F ⟶ G) :
    (functorTensorEquivOfBasis G b).symm.toLinearMap.comp (τ.app M).hom =
      (TensorProduct.map (τ.app (liftedUnit.{r, v} R)).hom LinearMap.id).comp
        (functorTensorEquivOfBasis F b).symm.toLinearMap := by
  ext y
  apply (functorTensorEquivOfBasis G b).injective
  change functorTensorEquivOfBasis G b
      ((functorTensorEquivOfBasis G b).symm (τ.app M y)) =
    functorTensorEquivOfBasis G b
      (TensorProduct.map (τ.app (liftedUnit.{r, v} R)).hom LinearMap.id
        ((functorTensorEquivOfBasis F b).symm y))
  rw [LinearEquiv.apply_symm_apply]
  have h := functorTensorComparison_natTrans_apply τ M
    ((functorTensorEquivOfBasis F b).symm y)
  change τ.app M
      (functorTensorEquivOfBasis F b ((functorTensorEquivOfBasis F b).symm y)) =
    functorTensorEquivOfBasis G b
      (TensorProduct.map (τ.app (liftedUnit.{r, v} R)).hom LinearMap.id
        ((functorTensorEquivOfBasis F b).symm y)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

end Basis

end ModuleCat
