/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.FunctorTensorRightScalars
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The right adjoint of tensor with right-factor scalars

The left adjoint is the existing tensor functor with its original carrier
and right-factor action. Its right adjoint is the original space of
coefficient-linear maps out of the given bimodule. The source-ring action
on this Hom space is precomposition, not an action on its codomain.
The adjunction uses the native balanced additive tensor lift.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

universe r l v w

variable (R : Type r) [CommRing R] (Λ : Type l) [Ring Λ]
  (M : Type v) [AddCommGroup M] [Module R M] [Module Λ M] [SMulCommClass Λ R M]

local instance : SMulCommClass R Λ M := SMulCommClass.symm Λ R M

/-- The source scalar acts on a coefficient-linear map by actual precomposition. -/
def homRightScalarsSmul (N : ModuleCat.{max v w} Λ) (a : R) (f : M →ₗ[Λ] N) :
    M →ₗ[Λ] N where
  toFun m := f (a • m)
  map_add' m n := by rw [smul_add, map_add]
  map_smul' b m := by
    change f (a • (b • m)) = b • f (a • m)
    rw [smul_comm a b m, map_smul]

/-- The commuting source-ring action on the unchanged Hom carrier. -/
@[instance_reducible]
def homRightScalarsModule (N : ModuleCat.{max v w} Λ) : Module R (M →ₗ[Λ] N) where
  smul := homRightScalarsSmul R Λ M N
  one_smul f := by
    ext m
    change f ((1 : R) • m) = f m
    rw [one_smul]
  mul_smul a b f := by
    ext m
    change f ((a * b) • m) = f (b • (a • m))
    rw [mul_smul, smul_comm a b m]
  smul_zero a := by ext m; rfl
  smul_add a f g := by ext m; rfl
  add_smul a b f := by
    ext m
    change f ((a + b) • m) = f (a • m) + f (b • m)
    rw [add_smul, map_add]
  zero_smul f := by
    ext m
    change f ((0 : R) • m) = 0
    rw [zero_smul, map_zero]

/-- The source-ring action on coefficient-linear maps by precomposition. -/
local instance homRightScalarsCarrierModule (N : ModuleCat.{max v w} Λ) :
    Module R (M →ₗ[Λ] N) :=
  homRightScalarsModule R Λ M N

/-- The right adjoint object is the original coefficient-linear Hom module. -/
abbrev homRightScalarsObj (N : ModuleCat.{max v w} Λ) : ModuleCat.{max v w} R :=
  ModuleCat.of R (M →ₗ[Λ] N)

/-- The right adjoint map is original postcomposition. -/
def homRightScalarsMap {N P : ModuleCat.{max v w} Λ} (f : N ⟶ P) :
    homRightScalarsObj R Λ M N ⟶ homRightScalarsObj R Λ M P :=
  ModuleCat.ofHom
    { toFun := fun g => f.hom.comp g
      map_add' := by intros; ext m; exact f.hom.map_add _ _
      map_smul' := by intros; ext m; rfl }

/-- The Hom functor with its genuine precomposition source-ring action. -/
def homRightScalarsFunctor : ModuleCat.{max v w} Λ ⥤ ModuleCat.{max v w} R where
  obj := homRightScalarsObj R Λ M
  map := homRightScalarsMap R Λ M
  map_id N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro m
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply LinearMap.ext
    intro m
    rfl

/-- The right-factor coefficient action for the adjunction. -/
local instance tensorRightScalarsAdjunctionModule (V : ModuleCat.{max v w} R) :
    Module Λ (V ⊗[R] M) :=
  TensorProduct.rightModule R Λ V M

/-- Currying retains the original tensor value on every pure tensor. -/
def tensorRightScalarsCurry (V : ModuleCat.{max v w} R) (N : ModuleCat.{max v w} Λ)
    (f : (tensorRightScalarsFunctor R Λ M).obj V ⟶ N) :
    V ⟶ (homRightScalarsFunctor R Λ M).obj N :=
  by
  let f₀ : (V ⊗[R] M) →ₗ[Λ] N := f.hom
  change V ⟶ homRightScalarsObj R Λ M N
  exact ModuleCat.ofHom
    { toFun := fun x =>
        { toFun := fun m => f₀ (x ⊗ₜ[R] m)
          map_add' := by
            intro m n
            rw [TensorProduct.tmul_add]
            exact f₀.map_add _ _
          map_smul' := by
            intro a m
            change f₀ (x ⊗ₜ[R] (a • m)) = a • f₀ (x ⊗ₜ[R] m)
            rw [← TensorProduct.rightModule_smul_tmul]
            exact f₀.map_smul a _ }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro m
        change f₀ ((x + y) ⊗ₜ[R] m) = f₀ (x ⊗ₜ[R] m) + f₀ (y ⊗ₜ[R] m)
        rw [TensorProduct.add_tmul]
        exact f₀.map_add _ _
      map_smul' := by
        intro a x
        apply LinearMap.ext
        intro m
        change f₀ ((a • x) ⊗ₜ[R] m) = f₀ (x ⊗ₜ[R] (a • m))
        rw [TensorProduct.smul_tmul] }

/-- The actual additive balanced pairing associated to a curried map. -/
def tensorRightScalarsPairing (V : ModuleCat.{max v w} R)
    (N : ModuleCat.{max v w} Λ) (f : V ⟶ (homRightScalarsFunctor R Λ M).obj N) :
    V →+ M →+ N := by
  let f₀ : V →ₗ[R] (M →ₗ[Λ] N) := f.hom
  exact
    { toFun := fun x => (f₀ x).toAddMonoidHom
      map_zero' := by
        apply AddMonoidHom.ext
        intro m
        exact congrArg (fun g : M →ₗ[Λ] N => g m) f₀.map_zero
      map_add' := by
        intro x y
        apply AddMonoidHom.ext
        intro m
        exact congrArg (fun g : M →ₗ[Λ] N => g m) (f₀.map_add x y) }

/-- Balance uses the original source-linearity of the curried map. -/
theorem tensorRightScalarsPairing_balanced (V : ModuleCat.{max v w} R)
    (N : ModuleCat.{max v w} Λ) (f : V ⟶ (homRightScalarsFunctor R Λ M).obj N)
    (a : R) (x : V) (m : M) :
    tensorRightScalarsPairing R Λ M V N f (a • x) m =
      tensorRightScalarsPairing R Λ M V N f x (a • m) :=
by
  let f₀ : V →ₗ[R] (M →ₗ[Λ] N) := f.hom
  exact congrArg (fun g : M →ₗ[Λ] N => g m) (f₀.map_smul a x)

/-- Uncurrying uses the original balanced additive tensor lift, which is
coefficient-linear because the pairing is coefficient-linear on its right. -/
def tensorRightScalarsUncurry (V : ModuleCat.{max v w} R)
    (N : ModuleCat.{max v w} Λ) (f : V ⟶ (homRightScalarsFunctor R Λ M).obj N) :
    (tensorRightScalarsFunctor R Λ M).obj V ⟶ N :=
  by
  let f₀ : V →ₗ[R] (M →ₗ[Λ] N) := f.hom
  let g : V ⊗[R] M →+ N :=
    TensorProduct.liftAddHom (tensorRightScalarsPairing R Λ M V N f)
      (tensorRightScalarsPairing_balanced R Λ M V N f)
  change tensorRightScalarsObj R Λ M V ⟶ N
  exact ModuleCat.ofHom
    { g with
      map_smul' := by
        intro a z
        change g (a • z) = a • g z
        induction z using TensorProduct.inductionOn with
        | tmul x m =>
            rw [TensorProduct.rightModule_smul_tmul]
            change (f₀ x) (a • m) = a • (f₀ x) m
            exact (f₀ x).map_smul a m
        | add z t hz ht =>
            rw [smul_add, g.map_add, g.map_add, hz, ht, smul_add] }

@[simp]
theorem tensorRightScalarsUncurry_tmul (V : ModuleCat.{max v w} R)
    (N : ModuleCat.{max v w} Λ) (f : V ⟶ (homRightScalarsFunctor R Λ M).obj N)
    (x : V) (m : M) :
    tensorRightScalarsUncurry R Λ M V N f (x ⊗ₜ[R] m) =
      (show M →ₗ[Λ] N from f.hom x) m := rfl

/-- The original tensor-Hom bijection, with no replacement tensor object. -/
def tensorRightScalarsHomEquiv (V : ModuleCat.{max v w} R)
    (N : ModuleCat.{max v w} Λ) :
    ((tensorRightScalarsFunctor R Λ M).obj V ⟶ N) ≃
      (V ⟶ (homRightScalarsFunctor R Λ M).obj N) where
  toFun := tensorRightScalarsCurry R Λ M V N
  invFun := tensorRightScalarsUncurry R Λ M V N
  left_inv f := by
    let f₀ : (V ⊗[R] M) →ₗ[Λ] N := f.hom
    let g₀ : (V ⊗[R] M) →ₗ[Λ] N :=
      (tensorRightScalarsUncurry R Λ M V N (tensorRightScalarsCurry R Λ M V N f)).hom
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change g₀ z = f₀ z
    induction z using TensorProduct.inductionOn with
    | tmul x m => rfl
    | add z t hz ht => rw [g₀.map_add, f₀.map_add, hz, ht]
  right_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (show M →ₗ[Λ] N from
      (tensorRightScalarsCurry R Λ M V N (tensorRightScalarsUncurry R Λ M V N f)).hom x) =
      (show M →ₗ[Λ] N from f.hom x)
    apply LinearMap.ext
    intro m
    rfl

/-- The Hom equivalence is natural in the original source maps. -/
theorem tensorRightScalarsHomEquiv_naturality_left_symm
    {V W : ModuleCat.{max v w} R} {N : ModuleCat.{max v w} Λ}
    (a : V ⟶ W) (b : W ⟶ (homRightScalarsFunctor R Λ M).obj N) :
    (tensorRightScalarsHomEquiv R Λ M V N).symm (a ≫ b) =
      (tensorRightScalarsFunctor R Λ M).map a ≫
        (tensorRightScalarsHomEquiv R Λ M W N).symm b := by
  let f₀ : (V ⊗[R] M) →ₗ[Λ] N :=
    ((tensorRightScalarsHomEquiv R Λ M V N).symm (a ≫ b)).hom
  let g₀ : (V ⊗[R] M) →ₗ[Λ] N :=
    ((tensorRightScalarsFunctor R Λ M).map a ≫
      (tensorRightScalarsHomEquiv R Λ M W N).symm b).hom
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change f₀ z = g₀ z
  induction z using TensorProduct.inductionOn with
  | tmul x m =>
      change (show M →ₗ[Λ] N from b.hom (a.hom x)) m =
        tensorRightScalarsUncurry R Λ M W N b
          (TensorProduct.map a.hom LinearMap.id (x ⊗ₜ[R] m))
      rw [TensorProduct.map_tmul]
      rfl
  | add z t hz ht => rw [f₀.map_add, g₀.map_add, hz, ht]

/-- The Hom equivalence is natural in the original target maps. -/
theorem tensorRightScalarsHomEquiv_naturality_right
    {V : ModuleCat.{max v w} R} {N P : ModuleCat.{max v w} Λ}
    (a : (tensorRightScalarsFunctor R Λ M).obj V ⟶ N) (b : N ⟶ P) :
    tensorRightScalarsHomEquiv R Λ M V P (a ≫ b) =
      tensorRightScalarsHomEquiv R Λ M V N a ≫
        (homRightScalarsFunctor R Λ M).map b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (show M →ₗ[Λ] P from
    (tensorRightScalarsHomEquiv R Λ M V P (a ≫ b)).hom x) =
    (show M →ₗ[Λ] P from
      (tensorRightScalarsHomEquiv R Λ M V N a ≫ (homRightScalarsFunctor R Λ M).map b).hom x)
  apply LinearMap.ext
  intro m
  rfl

/-- Tensor with the original right-factor scalars is left adjoint to the
original Hom module with precomposition source scalars. -/
def tensorRightScalarsAdjunction :
    tensorRightScalarsFunctor R Λ M ⊣ homRightScalarsFunctor.{r,l,v,w} R Λ M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorRightScalarsHomEquiv R Λ M
      homEquiv_naturality_left_symm := tensorRightScalarsHomEquiv_naturality_left_symm R Λ M
      homEquiv_naturality_right := tensorRightScalarsHomEquiv_naturality_right R Λ M }

/-- The existing tensor functor is a genuine left adjoint at the common value universe. -/
instance tensorRightScalarsFunctor_isLeftAdjoint :
    (tensorRightScalarsFunctor R Λ M :
      ModuleCat.{max v w} R ⥤ ModuleCat.{max v w} Λ).IsLeftAdjoint :=
  (tensorRightScalarsAdjunction R Λ M).isLeftAdjoint

/-- The actual adjunction unit sends a vector to the original pure-tensor map. -/
theorem tensorRightScalarsAdjunction_unit_apply (V : ModuleCat.{max v w} R)
    (x : V) (m : M) :
    (show M →ₗ[Λ] (tensorRightScalarsObj R Λ M V) from
      ((tensorRightScalarsAdjunction R Λ M).unit.app V).hom x) m = x ⊗ₜ[R] m := rfl

/-- The right-factor coefficient action on the tensor used by the counit. -/
local instance tensorRightScalarsHomCarrierModule (N : ModuleCat.{max v w} Λ) :
    Module Λ ((M →ₗ[Λ] N) ⊗[R] M) :=
  TensorProduct.rightModule R Λ (M →ₗ[Λ] N) M

/-- The actual adjunction counit is evaluation on original pure tensors. -/
theorem tensorRightScalarsAdjunction_counit_tmul (N : ModuleCat.{max v w} Λ)
    (f : M →ₗ[Λ] N) (m : M) :
    (show ((M →ₗ[Λ] N) ⊗[R] M) →ₗ[Λ] N from
      ((tensorRightScalarsAdjunction R Λ M).counit.app N).hom) (f ⊗ₜ[R] m) = f m := rfl

end ModuleCat
