/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Coalgebra.DualTensorHom
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Characters of a finite coalgebra dual over arbitrary coefficient algebras

The native tensor–Hom equivalence identifies algebra maps from the convolution
dual with native group-like elements after scalar extension. The coefficient
algebra is arbitrary, including the zero ring. The forward tensor is the
contraction of the original coevaluation; no basis occurs in the interface.
-/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct Module.Dual.FiniteDual

namespace TensorProduct

variable (k R V W : Type*) [CommRing k] [CommRing R] [Algebra k R]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The native tensor comparison for two scalar-extended modules. -/
def scalarTensorEquiv :
    (R ⊗[k] V) ⊗[R] (R ⊗[k] W) ≃ₗ[R] R ⊗[k] (V ⊗[k] W) :=
  AlgebraTensorModule.tensorTensorTensorComm k k R R R V R W ≪≫ₗ
    AlgebraTensorModule.congr (TensorProduct.lid R R) (LinearEquiv.refl k (V ⊗[k] W))

@[simp]
theorem scalarTensorEquiv_tmul (r s : R) (v : V) (w : W) :
    scalarTensorEquiv k R V W ((r ⊗ₜ[k] v) ⊗ₜ[R] (s ⊗ₜ[k] w)) =
      (r * s) ⊗ₜ[k] (v ⊗ₜ[k] w) := by
  simp [scalarTensorEquiv]

variable [Coalgebra k V]

/-- The native scalar-extension comultiplication has the original tensor formula. -/
theorem scalarTensorEquiv_comul (x : R ⊗[k] V) :
    scalarTensorEquiv k R V V (Coalgebra.comul (R := R) x) =
      (Coalgebra.comul (R := k) (A := V)).lTensor R x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul r v =>
    simp only [TensorProduct.comul_tmul, CommSemiring.comul_apply,
      LinearMap.lTensor_tmul]
    generalize Coalgebra.comul (R := k) v = z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul a b => simp [scalarTensorEquiv]

end TensorProduct

namespace Module.Dual

variable (k V R : Type*) [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [CommRing R] [Algebra k R]

/-- The original tensor–Hom and bidual equivalences, with coefficients on the left. -/
def tensorPairingEquiv : R ⊗[k] V ≃ₗ[k] (Dual k V →ₗ[k] R) :=
  TensorProduct.comm k R V ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv k V) (LinearEquiv.refl k R) ≪≫ₗ
      _root_.dualTensorHomEquiv k (Dual k V) R

@[simp]
theorem tensorPairingEquiv_tmul (r : R) (v : V) (f : Dual k V) :
    tensorPairingEquiv k V R (r ⊗ₜ[k] v) f = f v • r := rfl

/-- The whole tensor pairing commutes with the original coefficient-algebra map. -/
theorem tensorPairingEquiv_naturality {S : Type*} [CommRing S] [Algebra k S]
    (f : R →ₐ[k] S) (x : R ⊗[k] V) :
    tensorPairingEquiv k V S (TensorProduct.map f.toLinearMap LinearMap.id x) =
      f.toLinearMap.comp (tensorPairingEquiv k V R x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    ext g
    simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply, hx, hy]
  | tmul r v =>
    ext g
    simp

/-- The inverse pairing contracts the original native coevaluation. -/
theorem tensorPairingEquiv_symm_apply (f : Dual k V →ₗ[k] R) :
    (tensorPairingEquiv k V R).symm f =
      TensorProduct.comm k V R (f.lTensor V (coevaluation k V 1)) := by
  apply (tensorPairingEquiv k V R).injective
  rw [LinearEquiv.apply_symm_apply]
  have h (z : V ⊗[k] Dual k V) :
      tensorPairingEquiv k V R (TensorProduct.comm k V R (f.lTensor V z)) =
        f.comp (_root_.dualTensorHom k (Dual k V) (Dual k V)
          ((Module.Dual.eval k V).rTensor (Dual k V) z)) := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      ext g
      simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply, hx, hy]
    | tmul v g =>
      ext h
      simp [tensorPairingEquiv_tmul]
  rw [h, TensorProduct.dualTensorHom_eval_coevaluation, LinearMap.comp_id]

/-- The canonical tensor pairing detects tensors with arbitrary coefficient algebra. -/
theorem tensorPairingEquiv_tensor_ext {x y : R ⊗[k] (V ⊗[k] V)}
    (h : ∀ f g : Dual k V,
      tensorPairingEquiv k (V ⊗[k] V) R x
          (TensorProduct.dualDistrib k V V (f ⊗ₜ[k] g)) =
        tensorPairingEquiv k (V ⊗[k] V) R y
          (TensorProduct.dualDistrib k V V (f ⊗ₜ[k] g))) : x = y := by
  apply (tensorPairingEquiv k (V ⊗[k] V) R).injective
  ext p
  obtain ⟨z, rfl⟩ := (TensorProduct.dualDistribEquiv k V V).surjective p
  simp only [← LinearEquiv.coe_toLinearMap, TensorProduct.toLinearMap_dualDistribEquiv]
  induction z using TensorProduct.inductionOn with
  | tmul f g => exact h f g
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Tensoring two coefficient-valued functionals multiplies their original evaluations. -/
theorem tensorPairingEquiv_tensor (x y : R ⊗[k] V) (f g : Dual k V) :
    tensorPairingEquiv k (V ⊗[k] V) R
        (TensorProduct.scalarTensorEquiv k R V V (x ⊗ₜ[R] y))
        (TensorProduct.dualDistrib k V V (f ⊗ₜ[k] g)) =
      tensorPairingEquiv k V R x f * tensorPairingEquiv k V R y g := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ =>
    simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, h₁, h₂, add_mul]
  | tmul r v =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ =>
      simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, h₁, h₂, mul_add]
    | tmul s w =>
      simp [Algebra.smul_def, mul_mul_mul_comm]

variable [Coalgebra k V]

/-- The counit equation is exactly preservation of one by the coefficient functional. -/
theorem tensorPairingEquiv_one (x : R ⊗[k] V) :
    tensorPairingEquiv k V R x 1 = Coalgebra.counit (R := R) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Native scalar comultiplication is dual to the original convolution product. -/
theorem tensorPairingEquiv_comul (x : R ⊗[k] V) (f g : Dual k V) :
    tensorPairingEquiv k (V ⊗[k] V) R
        (TensorProduct.scalarTensorEquiv k R V V (Coalgebra.comul (R := R) x))
        (TensorProduct.dualDistrib k V V (f ⊗ₜ[k] g)) =
      tensorPairingEquiv k V R x (f * g) := by
  rw [TensorProduct.scalarTensorEquiv_comul]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul r v => simp [convolution_mul_apply]

/-- The group-like equations are precisely the algebra-map equations on the original dual. -/
theorem isGroupLikeElem_iff_tensorPairing (x : R ⊗[k] V) :
    IsGroupLikeElem R x ↔ tensorPairingEquiv k V R x 1 = 1 ∧
      ∀ f g, tensorPairingEquiv k V R x (f * g) =
        tensorPairingEquiv k V R x f * tensorPairingEquiv k V R x g := by
  constructor
  · intro h
    refine ⟨(tensorPairingEquiv_one k V R x).trans h.counit_eq_one, ?_⟩
    intro f g
    rw [← tensorPairingEquiv_comul, h.comul_eq_tmul_self, tensorPairingEquiv_tensor]
  · rintro ⟨hunit, hmul⟩
    refine ⟨(tensorPairingEquiv_one k V R x).symm.trans hunit, ?_⟩
    apply (TensorProduct.scalarTensorEquiv k R V V).injective
    apply tensorPairingEquiv_tensor_ext k V R
    intro f g
    rw [tensorPairingEquiv_comul, tensorPairingEquiv_tensor, hmul]

/-- Algebra maps from the native finite convolution dual represent native group-like elements. -/
def algHomGroupLikeEquiv : (Dual k V →ₐ[k] R) ≃ GroupLike R (R ⊗[k] V) where
  toFun f := ⟨(tensorPairingEquiv k V R).symm f.toLinearMap,
    (isGroupLikeElem_iff_tensorPairing k V R _).2 (by simp)⟩
  invFun x := AlgHom.ofLinearMap (tensorPairingEquiv k V R x.val)
    ((isGroupLikeElem_iff_tensorPairing k V R x.val).1 x.2).1
    ((isGroupLikeElem_iff_tensorPairing k V R x.val).1 x.2).2
  left_inv f := by
    ext v
    exact LinearMap.congr_fun ((tensorPairingEquiv k V R).apply_symm_apply f.toLinearMap) v
  right_inv x := by
    apply GroupLike.val_injective
    exact (tensorPairingEquiv k V R).symm_apply_apply x.val

/-- The represented group-like element is the contraction of the same native coevaluation. -/
theorem algHomGroupLikeEquiv_val (f : Dual k V →ₐ[k] R) :
    (algHomGroupLikeEquiv k V R f).val =
      TensorProduct.comm k V R (f.toLinearMap.lTensor V (coevaluation k V 1)) :=
  tensorPairingEquiv_symm_apply k V R f.toLinearMap

/-- The character equivalence is natural for arbitrary coefficient-algebra maps. -/
theorem algHomGroupLikeEquiv_naturality {S : Type*} [CommRing S] [Algebra k S]
    (f : Dual k V →ₐ[k] R) (g : R →ₐ[k] S) :
    (algHomGroupLikeEquiv k V S (g.comp f)).val =
      TensorProduct.map g.toLinearMap LinearMap.id (algHomGroupLikeEquiv k V R f).val := by
  apply (tensorPairingEquiv k V S).injective
  rw [tensorPairingEquiv_naturality]
  change tensorPairingEquiv k V S ((tensorPairingEquiv k V S).symm (g.comp f).toLinearMap) =
    g.toLinearMap.comp
      (tensorPairingEquiv k V R ((tensorPairingEquiv k V R).symm f.toLinearMap))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

end Module.Dual
