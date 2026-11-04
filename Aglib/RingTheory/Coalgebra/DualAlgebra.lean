/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# The convolution algebra on the native linear dual

The `FiniteDual` scope puts the native convolution operations on `Module.Dual`.
The carrier and its additive and scalar operations remain the original linear
dual. `WithConv` is used internally to reuse Mathlib's convolution laws.
No finiteness assumption is needed for this direction of duality.
-/

@[expose] public section

noncomputable section

open Module WithConv
open scoped TensorProduct

namespace Module.Dual

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A] [Coalgebra R A]

namespace FiniteDual

/-- The convolution ring structure on the original linear dual. -/
scoped instance convolutionRing : Ring (Dual R A) where
  __ := (WithConv.equiv (Dual R A)).symm.ring
  toAddCommGroup := inferInstance

/-- Convolution is compatible with the original pointwise scalar action on the dual. -/
scoped instance convolutionIsScalarTower : IsScalarTower R (Dual R A) (Dual R A) where
  smul_assoc r f g := by
    change (r • f) * g = r • (f * g)
    exact congrArg WithConv.ofConv (smul_mul_assoc r (toConv f) (toConv g))

/-- The original pointwise scalar action commutes with convolution multiplication. -/
scoped instance convolutionSMulCommClass : SMulCommClass R (Dual R A) (Dual R A) where
  smul_comm r f g := by
    change r • (f * g) = f * (r • g)
    exact (congrArg WithConv.ofConv (mul_smul_comm r (toConv f) (toConv g))).symm

/-- The scalar algebra structure induced by the original scalar multiplication. -/
scoped instance convolutionAlgebra : Algebra R (Dual R A) :=
  Algebra.ofModule
    (fun r f g => congrArg WithConv.ofConv (smul_mul_assoc r (toConv f) (toConv g)))
    (fun r f g => congrArg WithConv.ofConv (mul_smul_comm r (toConv f) (toConv g)))

/-- Cocommutativity makes the convolution product on the original dual commutative. -/
scoped instance convolutionCommRing [Coalgebra.IsCocomm R A] :
    CommRing (Dual R A) where
  __ := convolutionRing
  mul_comm f g := congrArg WithConv.ofConv (mul_comm (toConv f) (toConv g))

end FiniteDual

open scoped FiniteDual

@[simp]
theorem convolution_one_apply (a : A) : (1 : Dual R A) a = Coalgebra.counit a := rfl

@[simp]
theorem convolution_algebraMap_apply (r : R) (a : A) :
    algebraMap R (Dual R A) r a = r * Coalgebra.counit a := by
  rfl

/-- Evaluation of convolution is the canonical tensor-dual pairing against comultiplication. -/
theorem convolution_mul_apply (f g : Dual R A) (a : A) :
    (f * g) a =
      TensorProduct.dualDistrib R A A (f ⊗ₜ g) (Coalgebra.comul a) := by
  change LinearMap.mul' R R (TensorProduct.map f g (Coalgebra.comul a)) = _
  have h (x : A ⊗[R] A) :
      LinearMap.mul' R R (TensorProduct.map f g x) =
        TensorProduct.dualDistrib R A A (f ⊗ₜ g) x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp
    | add x y hx hy => simp [hx, hy]
  exact h _

variable (R A) in
/-- Multiplication on the dual contracts a tensor against the original comultiplication. -/
theorem mul'_apply (x : Dual R A ⊗[R] Dual R A) (a : A) :
    LinearMap.mul' R (Dual R A) x a =
      TensorProduct.dualDistrib R A A x (Coalgebra.comul a) := by
  induction x using TensorProduct.inductionOn with
  | tmul f g => exact convolution_mul_apply f g a
  | add x y hx hy => simp [hx, hy]

end Module.Dual

namespace CoalgHom

open scoped Module.Dual.FiniteDual

variable {R A B C : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [Coalgebra R A]
  [AddCommGroup B] [Module R B] [Coalgebra R B]
  [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- The transpose of a coalgebra homomorphism on the original convolution dual algebras. -/
def dualAlgHom (f : A →ₗc[R] B) : Dual R B →ₐ[R] Dual R A where
  __ := f.toLinearMap.dualMap
  map_zero' := by ext; rfl
  map_one' := by ext; simp
  map_mul' g h := LinearMap.convMul_comp_coalgHom_distrib (toConv g) (toConv h) f
  commutes' r := by ext; simp

@[simp]
theorem dualAlgHom_apply (f : A →ₗc[R] B) (g : Dual R B) (a : A) :
    f.dualAlgHom g a = g (f a) := rfl

@[simp]
theorem dualAlgHom_id : (CoalgHom.id R A).dualAlgHom = AlgHom.id R (Dual R A) := by
  ext
  rfl

@[simp]
theorem dualAlgHom_comp (f : A →ₗc[R] B) (g : B →ₗc[R] C) :
    (g.comp f).dualAlgHom = f.dualAlgHom.comp g.dualAlgHom := by
  ext
  rfl

end CoalgHom
