/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.RootBaseChange
public import Aglib.RingTheory.IntegralClosure.FiniteOverNormal
public import Aglib.RingTheory.Henselian.StrictHenselization.IntegralClosure

/-! # The original normalization comparison after pointed root base change

Only the actual pointed etale-colimit comparison is used. The two root
algebras are integral over their coefficient rings; changing those integral
coefficients does not alter integral elements. Pushout cancellation then
identifies the resulting map with the native tensor-to-integral-closure map.
No normality, DVR structure, or finiteness of the normalization is assumed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.Kummer

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  (N : ℕ) (π : R)

local notation "C" => GeometricEtaleColimit R Ω
local notation "T" => RootAlgebra N π
local notation "T'" => RootAlgebra N (algebraMap R C π)

local instance : Algebra T T' := rootBaseChangeAlgebra C N π
local instance : IsScalarTower R T T' :=
  IsScalarTower.of_algebraMap_eq fun r => ((rootBaseChangeHom C N π).commutes r).symm

/-- The literal coefficient-changed root algebra is the original root pushout. -/
theorem strictRoot_isPushout : Algebra.IsPushout R C T T' := by
  let : Algebra T (C ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  apply Algebra.IsPushout.of_equiv (genericRootEquiv (K := C) N π)
  exact RingHom.ext fun _ => rfl

variable (A : Type u) [CommRing A] [Algebra (RootAlgebra N π) A] [Algebra R A]
  [IsScalarTower R (RootAlgebra N π) A]

/-- The native normalization comparison is bijective for the unchanged root
map over the actual pointed etale colimit. -/
theorem strictRoot_toIntegralClosure_bijective (hN : 0 < N) :
    Function.Bijective (_root_.TensorProduct.toIntegralClosure T T' A) := by
  let : Module.Finite R T := root_finite N hN π
  let : Module.Finite C T' := root_finite N hN (algebraMap R C π)
  let : Algebra.IsPushout R C T T' := strictRoot_isPushout R Ω N π
  let cB := Algebra.IsPushout.cancelBaseChangeAlg R C T T' (integralClosure T A)
  let cA := Algebra.IsPushout.cancelBaseChangeAlg R C T T' A
  let e : T' ⊗[T] integralClosure T A ≃ₐ[C]
      integralClosure T' (T' ⊗[T] A) :=
    cB.trans ((Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[C] C)
      (integralClosure.equivOfIntegral R T A)).trans
      ((GeometricEtaleColimit.integralClosureEquiv R Ω A).trans
        (cA.symm.mapIntegralClosure.trans
          (integralClosure.equivOfIntegral C T' (T' ⊗[T] A)).symm)))
  have he : ∀ x, e x = _root_.TensorProduct.toIntegralClosure T T' A x := by
    intro x
    obtain ⟨y, rfl⟩ := cB.symm.surjective x
    induction y using TensorProduct.inductionOn with
    | tmul c b =>
      apply Subtype.ext
      simp only [e, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
      simp [cA, cB, Algebra.TensorProduct.congr_apply,
        _root_.TensorProduct.toIntegralClosure]
    | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  exact (show (e : _ → _) = _root_.TensorProduct.toIntegralClosure T T' A from
    funext he) ▸ e.bijective

/-- This equivalence is the original tensor-to-integral-closure map, linear
over the literal coefficient-changed root algebra. -/
def strictRoot_integralClosureEquiv (hN : 0 < N) :
    T' ⊗[T] integralClosure T A ≃ₐ[T'] integralClosure T' (T' ⊗[T] A) :=
  AlgEquiv.ofBijective (_root_.TensorProduct.toIntegralClosure T T' A)
    (strictRoot_toIntegralClosure_bijective R Ω N π A hN)

/-- Original integral elements and root-base coefficients are unchanged. -/
@[simp] theorem strictRoot_integralClosureEquiv_tmul_val (hN : 0 < N)
    (t : T') (b : integralClosure T A) :
    (strictRoot_integralClosureEquiv R Ω N π A hN (t ⊗ₜ[T] b) : T' ⊗[T] A) =
      t ⊗ₜ[T] (b : A) := rfl

end Algebra.Kummer
