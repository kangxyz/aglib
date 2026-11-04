/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The coalgebra dual to a finite-dimensional algebra

The carrier is the native linear dual. Comultiplication is the transpose of
multiplication through the canonical tensor-dual equivalence, and the counit
is evaluation at one. Algebra homomorphisms induce the actual contravariant
coalgebra maps. No basis is part of any construction or statement.
-/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct

namespace TensorProduct

variable {k M N P : Type*} [Field k]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  [AddCommGroup P] [Module k P]

/-- The canonical tensor pairing detects tensors of finite-dimensional duals. -/
theorem dual_ext [FiniteDimensional k M] [FiniteDimensional k N]
    {x y : Dual k M ⊗[k] Dual k N}
    (h : ∀ m n, dualDistrib k M N x (m ⊗ₜ n) =
      dualDistrib k M N y (m ⊗ₜ n)) : x = y := by
  apply (dualDistribEquiv k M N).injective
  apply TensorProduct.ext'
  intro m n
  simpa only [← LinearEquiv.coe_toLinearMap, toLinearMap_dualDistribEquiv] using h m n

/-- Tensor-dual evaluation commutes with the associator, with the original order of factors. -/
theorem dualDistrib_assoc_tmul
    (x : Dual k M ⊗[k] Dual k N) (f : Dual k P) (m : M) (n : N) (p : P) :
    dualDistrib k M (N ⊗[k] P)
      (map LinearMap.id (dualDistrib k N P)
        (TensorProduct.assoc k (Dual k M) (Dual k N) (Dual k P) (x ⊗ₜ f)))
      (m ⊗ₜ (n ⊗ₜ p)) = dualDistrib k M N x (m ⊗ₜ n) * f p := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [mul_assoc]
  | add x y hx hy => simp [add_tmul, hx, hy, add_mul]

/-- The tensor-dual pairing is natural for the actual transposed linear maps. -/
theorem dualDistrib_map_dualMap
    {M' N' : Type*} [AddCommGroup M'] [Module k M']
    [AddCommGroup N'] [Module k N'] (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (x : Dual k M' ⊗[k] Dual k N') (m : M) (n : N) :
    dualDistrib k M N (map f.dualMap g.dualMap x) (m ⊗ₜ n) =
      dualDistrib k M' N' x (f m ⊗ₜ g n) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

/-- Naturality of the tensor-dual pairing on an arbitrary tensor. -/
theorem dualDistrib_map_dualMap_apply
    {M' N' : Type*} [AddCommGroup M'] [Module k M']
    [AddCommGroup N'] [Module k N'] (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (x : Dual k M' ⊗[k] Dual k N') (z : M ⊗[k] N) :
    dualDistrib k M N (map f.dualMap g.dualMap x) z =
      dualDistrib k M' N' x (map f g z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m n => exact dualDistrib_map_dualMap f g x m n
  | add x y hx hy => simp [hx, hy]

/-- The tensor pairing with two bidual evaluations is the original tensor pairing. -/
theorem dualDistrib_eval_tmul (x : Dual k M ⊗[k] Dual k N) (m : M) (n : N) :
    dualDistrib k (Dual k M) (Dual k N)
      (Module.Dual.eval k M m ⊗ₜ[k] Module.Dual.eval k N n) x =
      dualDistrib k M N x (m ⊗ₜ[k] n) := by
  induction x using TensorProduct.inductionOn with
  | tmul f g => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Tensoring the native bidual evaluations preserves the original tensor pairing. -/
theorem dualDistrib_map_eval (x : M ⊗[k] N) (f : Dual k M) (g : Dual k N) :
    dualDistrib k (Dual k M) (Dual k N)
      (map (Module.Dual.eval k M) (Module.Dual.eval k N) x) (f ⊗ₜ[k] g) =
      dualDistrib k M N (f ⊗ₜ[k] g) x := by
  induction x using TensorProduct.inductionOn with
  | tmul m n => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end TensorProduct

namespace Module.Dual

variable (k A : Type*) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- The transpose of algebra multiplication through the canonical tensor-dual equivalence. -/
def coalgebraComul : Dual k A →ₗ[k] Dual k A ⊗[k] Dual k A :=
  (TensorProduct.dualDistribEquiv k A A).symm.toLinearMap ∘ₗ
    (LinearMap.mul' k A).dualMap

/-- The counit on the dual of an algebra is evaluation at its unit. -/
def coalgebraCounit : Dual k A →ₗ[k] k := eval k A 1

omit [FiniteDimensional k A] in
@[simp]
theorem coalgebraCounit_apply (f : Dual k A) : coalgebraCounit k A f = f 1 := rfl

@[simp]
theorem dualDistrib_coalgebraComul (f : Dual k A) (a b : A) :
    TensorProduct.dualDistrib k A A (coalgebraComul k A f) (a ⊗ₜ b) = f (a * b) := by
  change TensorProduct.dualDistrib k A A
      ((TensorProduct.dualDistribEquiv k A A).symm ((LinearMap.mul' k A).dualMap f))
      (a ⊗ₜ b) = _
  rw [← TensorProduct.toLinearMap_dualDistribEquiv]
  exact DFunLike.congr_fun
    ((TensorProduct.dualDistribEquiv k A A).apply_symm_apply ((LinearMap.mul' k A).dualMap f))
    (a ⊗ₜ b)

/-- The dual comultiplication is the transpose of multiplication on every tensor. -/
theorem dualDistrib_coalgebraComul_apply (f : Dual k A) (z : A ⊗[k] A) :
    TensorProduct.dualDistrib k A A (coalgebraComul k A f) z =
      f (LinearMap.mul' k A z) := by
  change TensorProduct.dualDistrib k A A
      ((TensorProduct.dualDistribEquiv k A A).symm ((LinearMap.mul' k A).dualMap f)) z = _
  rw [← TensorProduct.toLinearMap_dualDistribEquiv]
  exact DFunLike.congr_fun
    ((TensorProduct.dualDistribEquiv k A A).apply_symm_apply ((LinearMap.mul' k A).dualMap f)) z

theorem coalgebraComul_coassoc :
    (TensorProduct.assoc k (Dual k A) (Dual k A) (Dual k A)).toLinearMap ∘ₗ
      (coalgebraComul k A).rTensor (Dual k A) ∘ₗ coalgebraComul k A =
    (coalgebraComul k A).lTensor (Dual k A) ∘ₗ coalgebraComul k A := by
  ext f
  apply (TensorProduct.congr (LinearEquiv.refl k (Dual k A))
    (TensorProduct.dualDistribEquiv k A A)).injective
  apply TensorProduct.dual_ext
  intro a z
  simp only [← LinearEquiv.coe_toLinearMap, TensorProduct.toLinearMap_congr,
    LinearEquiv.refl_toLinearMap, TensorProduct.toLinearMap_dualDistribEquiv]
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | tmul b c =>
    have hleft (x : Dual k A ⊗[k] Dual k A) :
        TensorProduct.dualDistrib k A (A ⊗[k] A)
          (TensorProduct.map LinearMap.id (TensorProduct.dualDistrib k A A)
            (TensorProduct.assoc k (Dual k A) (Dual k A) (Dual k A)
              ((coalgebraComul k A).rTensor (Dual k A) x)))
          (a ⊗ₜ (b ⊗ₜ c)) =
        TensorProduct.dualDistrib k A A x ((a * b) ⊗ₜ c) := by
      induction x using TensorProduct.inductionOn with
      | tmul g h =>
        simp only [LinearMap.rTensor_tmul, TensorProduct.dualDistrib_assoc_tmul,
          dualDistrib_coalgebraComul, TensorProduct.dualDistrib_apply]
      | add x y hx hy => simp [hx, hy]
    have hright (x : Dual k A ⊗[k] Dual k A) :
        TensorProduct.dualDistrib k A (A ⊗[k] A)
          (TensorProduct.map LinearMap.id (TensorProduct.dualDistrib k A A)
            ((coalgebraComul k A).lTensor (Dual k A) x))
          (a ⊗ₜ (b ⊗ₜ c)) =
        TensorProduct.dualDistrib k A A x (a ⊗ₜ (b * c)) := by
      induction x using TensorProduct.inductionOn with
      | tmul g h => simp
      | add x y hx hy =>
        simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hx hy
    change TensorProduct.dualDistrib k A (A ⊗[k] A)
        (TensorProduct.map LinearMap.id (TensorProduct.dualDistrib k A A)
          (TensorProduct.assoc k (Dual k A) (Dual k A) (Dual k A)
            ((coalgebraComul k A).rTensor (Dual k A) (coalgebraComul k A f))))
        (a ⊗ₜ (b ⊗ₜ c)) =
      TensorProduct.dualDistrib k A (A ⊗[k] A)
        (TensorProduct.map LinearMap.id (TensorProduct.dualDistrib k A A)
          ((coalgebraComul k A).lTensor (Dual k A) (coalgebraComul k A f)))
        (a ⊗ₜ (b ⊗ₜ c))
    rw [hleft, hright, dualDistrib_coalgebraComul, dualDistrib_coalgebraComul, mul_assoc]

theorem coalgebraCounit_rTensor_comul :
    (coalgebraCounit k A).rTensor (Dual k A) ∘ₗ coalgebraComul k A =
      TensorProduct.mk k k (Dual k A) 1 := by
  ext f
  apply (TensorProduct.lid k (Dual k A)).injective
  ext a
  have h (x : Dual k A ⊗[k] Dual k A) :
      TensorProduct.lid k (Dual k A) ((coalgebraCounit k A).rTensor (Dual k A) x) a =
        TensorProduct.dualDistrib k A A x (1 ⊗ₜ a) := by
    induction x using TensorProduct.inductionOn with
    | tmul g h => simp
    | add x y hx hy => simp [hx, hy]
  simpa using h (coalgebraComul k A f)

theorem coalgebraCounit_lTensor_comul :
    (coalgebraCounit k A).lTensor (Dual k A) ∘ₗ coalgebraComul k A =
      (TensorProduct.mk k (Dual k A) k).flip 1 := by
  ext f
  apply (TensorProduct.rid k (Dual k A)).injective
  ext a
  have h (x : Dual k A ⊗[k] Dual k A) :
      TensorProduct.rid k (Dual k A) ((coalgebraCounit k A).lTensor (Dual k A) x) a =
        TensorProduct.dualDistrib k A A x (a ⊗ₜ 1) := by
    induction x using TensorProduct.inductionOn with
    | tmul g h => simp [mul_comm]
    | add x y hx hy => simp [hx, hy]
  simpa using h (coalgebraComul k A f)

/-- The canonical coalgebra on the linear dual of a finite-dimensional algebra. -/
instance finiteCoalgebra : Coalgebra k (Dual k A) where
  comul := coalgebraComul k A
  counit := coalgebraCounit k A
  coassoc := coalgebraComul_coassoc k A
  rTensor_counit_comp_comul := coalgebraCounit_rTensor_comul k A
  lTensor_counit_comp_comul := coalgebraCounit_lTensor_comul k A

@[simp]
theorem counit_apply (f : Dual k A) : Coalgebra.counit (R := k) f = f 1 := rfl

@[simp]
theorem dualDistrib_comul (f : Dual k A) (a b : A) :
    TensorProduct.dualDistrib k A A (Coalgebra.comul f) (a ⊗ₜ b) = f (a * b) :=
  dualDistrib_coalgebraComul k A f a b

theorem dualDistrib_comul_apply (f : Dual k A) (z : A ⊗[k] A) :
    TensorProduct.dualDistrib k A A (Coalgebra.comul f) z =
      f (LinearMap.mul' k A z) :=
  dualDistrib_coalgebraComul_apply k A f z

end Module.Dual

namespace Module.Dual

variable (k A : Type*) [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]

/-- The dual of a commutative finite-dimensional algebra is cocommutative. -/
instance finiteCoalgebraIsCocomm : Coalgebra.IsCocomm k (Dual k A) where
  comm_comp_comul := by
    ext f
    apply TensorProduct.dual_ext
    intro a b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← TensorProduct.dualDistrib_apply_comm]
    simp [mul_comm]

end Module.Dual

namespace AlgHom

variable {k A B C : Type*} [Field k]
  [Ring A] [Algebra k A] [FiniteDimensional k A]
  [Ring B] [Algebra k B] [FiniteDimensional k B]
  [Ring C] [Algebra k C] [FiniteDimensional k C]

/-- The actual transpose of an algebra map, as a homomorphism of finite dual coalgebras. -/
def dualCoalgHom (f : A →ₐ[k] B) : Dual k B →ₗc[k] Dual k A where
  __ := f.toLinearMap.dualMap
  counit_comp := by ext; simp
  map_comp_comul := by
    ext g
    apply TensorProduct.dual_ext
    intro a b
    simp [TensorProduct.dualDistrib_map_dualMap]

@[simp]
theorem dualCoalgHom_apply (f : A →ₐ[k] B) (g : Dual k B) (a : A) :
    f.dualCoalgHom g a = g (f a) := rfl

@[simp]
theorem dualCoalgHom_id : (AlgHom.id k A).dualCoalgHom = CoalgHom.id k (Dual k A) := by
  ext
  rfl

@[simp]
theorem dualCoalgHom_comp (f : A →ₐ[k] B) (g : B →ₐ[k] C) :
    (g.comp f).dualCoalgHom = f.dualCoalgHom.comp g.dualCoalgHom := by
  ext
  rfl

end AlgHom
