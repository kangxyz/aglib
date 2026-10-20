/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.Automorphism.BaseChange
public import Mathlib.Tactic.Ring

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/Automorphism/UnitPath.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`01d5104a393047aec103a980d1d1a1a41ec90df1852f0256f50793afdf3780d9`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Module.Automorphism.UnitPath
open Module.Automorphism
open scoped _root_.TensorProduct
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def upper (c : R) : (R × R) ≃ₗ[R] (R × R) where
  toFun v := (v.1 + c * v.2, v.2)
  invFun v := (v.1 - c * v.2, v.2)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp
  map_add' v w := by
    apply Prod.ext
    · change v.1 + w.1 + c * (v.2 + w.2) =
        (v.1 + c * v.2) + (w.1 + c * w.2)
      ring
    · rfl
  map_smul' r v := by
    apply Prod.ext
    · change r * v.1 + c * (r * v.2) = r * (v.1 + c * v.2)
      ring
    · rfl

def lower (c : R) : (R × R) ≃ₗ[R] (R × R) where
  toFun v := (v.1, v.2 + c * v.1)
  invFun v := (v.1, v.2 - c * v.1)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp
  map_add' v w := by
    apply Prod.ext
    · rfl
    · change v.2 + w.2 + c * (v.1 + w.1) =
        (v.2 + c * v.1) + (w.2 + c * w.1)
      ring
  map_smul' r v := by
    apply Prod.ext
    · rfl
    · change r * v.2 + c * (r * v.1) = r * (v.2 + c * v.1)
      ring

/-- At t=1 this is diag(u,u⁻¹); at t=0 it is identity.
Composition is written in application order (rightmost matrix first). -/
def specialPath (u : Rˣ) (t : R) : (R × R) ≃ₗ[R] (R × R) :=
  upper (-t) ≪≫ₗ lower t ≪≫ₗ upper (-t) ≪≫ₗ upper (t * (u : R)) ≪≫ₗ
    lower (-(t * (↑u⁻¹ : R))) ≪≫ₗ upper (t * (u : R))

@[simp] theorem smulUnit_apply (u : Rˣ) (x : R) :
    LinearEquiv.smulOfUnit u x = (u : R) * x := rfl

theorem specialPath_zero (u : Rˣ) :
    specialPath u 0 = LinearEquiv.refl R (R × R) := by
  ext v <;> simp [specialPath, upper, lower]

theorem specialPath_one (u : Rˣ) :
    specialPath u 1 = (LinearEquiv.smulOfUnit u).prodCongr
      (LinearEquiv.smulOfUnit u⁻¹) := by
  ext v
  · simp only [specialPath, LinearEquiv.trans_apply, upper, lower,
      LinearEquiv.coe_mk, LinearEquiv.prodCongr_apply, smulUnit_apply,
      one_mul]
    simp [mul_add, mul_neg, ← mul_assoc]
  · simp only [specialPath, LinearEquiv.trans_apply, upper, lower,
      LinearEquiv.coe_mk, LinearEquiv.prodCongr_apply, smulUnit_apply,
      one_mul]
    simp [mul_add, mul_neg, ← mul_assoc]

/-- The determinant-constant elementary path from diag(ab,1) to diag(a,b). -/
def pairPath (a b : Rˣ) (t : R) : (R × R) ≃ₗ[R] (R × R) :=
  (specialPath b⁻¹ t).trans
    ((LinearEquiv.smulOfUnit (a * b)).prodCongr (LinearEquiv.refl R R))

theorem pairPath_zero (a b : Rˣ) : pairPath a b 0 =
    ((Object.unit (a*b)).sum (Object.unit 1)).a := by
  rw [pairPath, specialPath_zero]
  ext v <;> simp [Object.unit]

theorem pairPath_one (a b : Rˣ) : pairPath a b 1 =
    ((Object.unit a).sum (Object.unit b)).a := by
  rw [pairPath, specialPath_one]
  ext v <;> simp [Object.unit, mul_assoc]

def pathObject (a b : Rˣ) (t : R) : Object R where
  carrier := R × R
  a := pairPath a b t

theorem pairPath_natural (f : R →+* S) (a b : Rˣ) (t : R) (v : R × R) :
    Prod.map f f (pairPath a b t v) =
      pairPath (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) (f t)
        (Prod.map f f v) := by
  ext <;> simp [pairPath, specialPath, upper, lower, map_add, map_mul, map_neg]

/-- The literal free-module base-change equivalence, including the operator. -/
def baseChangePathIso (f : R →+* S) (a b : Rˣ) (t : R) :
    letI := f.toAlgebra
    Object.Iso ((pathObject a b t).baseChange S)
      (pathObject (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) (f t)) := by
  letI := f.toAlgebra
  let e : S ⊗[R] (R × R) ≃ₗ[S] (S × S) :=
    (TensorProduct.prodRight R S S R R).trans
      ((TensorProduct.AlgebraTensorModule.rid R S S).prodCongr
        (TensorProduct.AlgebraTensorModule.rid R S S))
  have hf : algebraMap R S = f := rfl
  refine ⟨e, ?_⟩
  intro z
  have h : e.toLinearMap.comp ((pairPath a b t).toLinearMap.baseChange S) =
      (pairPath (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) (f t)).toLinearMap.comp
        e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s v
    ext
    · simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
        LinearEquiv.coe_coe, e, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul,
        LinearEquiv.prodCongr_apply, TensorProduct.AlgebraTensorModule.rid_tmul]
      simp [pairPath, specialPath, upper, lower, Algebra.smul_def,
        map_add, map_mul, map_neg, hf]
      ring
    · simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
        LinearEquiv.coe_coe, e, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul,
        LinearEquiv.prodCongr_apply, TensorProduct.AlgebraTensorModule.rid_tmul]
      simp [pairPath, specialPath, upper, lower, Algebra.smul_def,
        map_add, map_mul, map_neg, hf]
      ring
  exact LinearMap.congr_fun h z

end Module.Automorphism.UnitPath
