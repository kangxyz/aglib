/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Absorbing parameter coordinates into the coefficient ring

An actual generating family remains generating after coordinates that already come
from the coefficient algebra are removed. The substitution commutes with evaluation,
so its inverse image of the new relation ideal is exactly the old relation ideal.
This does not assert a Fitting-ideal identity for an arbitrary tower of algebras.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace MvPolynomial

variable {R A α β : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Substitute coefficient parameters for the right-hand coordinates of a sum. -/
def parameterSubstitution (a : α → A) :
    MvPolynomial (β ⊕ α) R →ₐ[R] MvPolynomial β A :=
  aeval (Sum.elim X (fun i => C (a i)))

/-- For polynomial parameters, substitution is the native iterated-polynomial equivalence. -/
theorem parameterSubstitution_X :
    parameterSubstitution (R := R) (β := β) (X : α → MvPolynomial α R) =
      (sumAlgEquiv R β α).toAlgHom := by
  ext i
  cases i <;> simp [parameterSubstitution]

end MvPolynomial

namespace Algebra.Generators

variable {R A B α β : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Evaluation after parameter substitution is the original evaluation map. -/
theorem aeval_parameterSubstitution (P : Generators R B (β ⊕ α)) (a : α → A)
    (ha : ∀ i, algebraMap A B (a i) = P.val (.inr i)) (f : MvPolynomial (β ⊕ α) R) :
    aeval (R := A) (fun j => P.val (.inl j)) (parameterSubstitution a f) =
      aeval P.val f := by
  have he : ((aeval (R := A) (fun j => P.val (.inl j))).restrictScalars R).comp
      (parameterSubstitution a) = aeval P.val := by
    ext i
    cases i <;> simp [parameterSubstitution, ha]
  exact DFunLike.congr_fun he f

/-- Remove coordinates that are supplied by the coefficient algebra, using the original
section to construct the new generating family. -/
def absorbParameters (P : Generators R B (β ⊕ α)) (a : α → A)
    (ha : ∀ i, algebraMap A B (a i) = P.val (.inr i)) : Generators A B β where
  val j := P.val (.inl j)
  σ' b := parameterSubstitution a (P.σ b)
  aeval_val_σ' b := by
    rw [P.aeval_parameterSubstitution a ha, P.aeval_val_σ]

/-- The remaining coordinates are unchanged. -/
@[simp] theorem absorbParameters_val (P : Generators R B (β ⊕ α)) (a : α → A)
    (ha : ∀ i, algebraMap A B (a i) = P.val (.inr i)) (j : β) :
    (P.absorbParameters a ha).val j = P.val (.inl j) := rfl

/-- The inverse image of the actual new relation ideal is the original relation ideal. -/
theorem comap_ker_absorbParameters (P : Generators R B (β ⊕ α)) (a : α → A)
    (ha : ∀ i, algebraMap A B (a i) = P.val (.inr i)) :
    Ideal.comap (parameterSubstitution a).toRingHom (P.absorbParameters a ha).ker =
      P.ker := by
  ext f
  simp only [Ideal.mem_comap, ker_eq_ker_aeval_val, RingHom.mem_ker]
  change aeval (R := A) (fun j => P.val (.inl j)) (parameterSubstitution a f) = 0 ↔ _
  rw [P.aeval_parameterSubstitution a ha]

/-- Any point of the algebra evaluates a substituted polynomial at the unchanged
remaining coordinates exactly as it evaluates the original polynomial. -/
theorem eval_absorbParameters {S : Type*} [CommRing S] [Algebra A S]
    (P : Generators R B (β ⊕ α)) (a : α → A)
    (ha : ∀ i, algebraMap A B (a i) = P.val (.inr i)) (χ : B →ₐ[A] S)
    (f : MvPolynomial (β ⊕ α) R) :
    aeval (R := A) (fun j => χ (P.val (.inl j))) (parameterSubstitution a f) =
      χ (aeval P.val f) := by
  rw [← comp_aeval_apply, P.aeval_parameterSubstitution a ha]

/-- For polynomial parameters, every new relation is the image of an old relation. -/
theorem map_ker_absorbPolynomialParameters
    [Algebra (MvPolynomial α R) B] [IsScalarTower R (MvPolynomial α R) B]
    (P : Generators R B (β ⊕ α))
    (ha : ∀ i, algebraMap (MvPolynomial α R) B (X i) = P.val (.inr i)) :
    Ideal.map (parameterSubstitution (R := R) (β := β) X).toRingHom P.ker =
      (P.absorbParameters X ha).ker := by
  have hs : Function.Surjective
      (parameterSubstitution (R := R) (β := β) (X : α → MvPolynomial α R)) := by
    rw [parameterSubstitution_X]
    exact (sumAlgEquiv R β α).surjective
  rw [← P.comap_ker_absorbParameters X ha]
  exact Ideal.map_comap_of_surjective _ hs _

/-- The relative Jacobian in the remaining coordinates is the corresponding part of
 the original Jacobian, evaluated in the same algebra. -/
theorem aeval_pderiv_absorbPolynomialParameters
    [Algebra (MvPolynomial α R) B] [IsScalarTower R (MvPolynomial α R) B]
    (P : Generators R B (β ⊕ α))
    (ha : ∀ i, algebraMap (MvPolynomial α R) B (X i) = P.val (.inr i))
    (f : MvPolynomial (β ⊕ α) R) (j : β) :
    aeval (R := MvPolynomial α R) (P.absorbParameters X ha).val
      (pderiv j (parameterSubstitution (X : α → MvPolynomial α R) f)) =
      aeval P.val (pderiv (.inl j) f) := by
  change aeval (R := MvPolynomial α R) (fun b => P.val (.inl b))
    (pderiv j (parameterSubstitution (X : α → MvPolynomial α R) f)) = _
  have hd := pderiv_sumAlgEquiv j f
  have he := P.aeval_parameterSubstitution (X : α → MvPolynomial α R) ha
    (pderiv (.inl j) f)
  rw [parameterSubstitution_X] at he ⊢
  exact (congrArg (aeval (R := MvPolynomial α R) (fun b => P.val (.inl b))) hd).trans he

end Algebra.Generators
