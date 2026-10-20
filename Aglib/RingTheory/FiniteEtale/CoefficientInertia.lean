/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Unramified.Rigidity
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Invariant.Basic

/-!
Auxiliary local H1/torsor construction for
`K2-018#prop:k2018-arithmetic-characters` at source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

# Coefficient inertia from actual finite etaleness

Finite etale H/R is the SAME coefficient algebra. A point of its actual generic
fiber restricts canonically to H -> integralClosure R Omega by finiteness.
After localization at the SAME literal prime Q, inertia equality in the residue
and the accepted P16 unramified-point uniqueness theorem force equality.
No completeness, perfect residue, rational point, or coefficient-inertia input
is used to derive coefficient-inertia triviality.

P16 dependency: FiniteEtalePointSpecialization.lean, SHA256
40b4e6687a3ade8042094ba2eef19bb23cc6d61b84283648b6aa42dd1c20ef71.
Its general local-target uniqueness theorem is imported, not duplicated.
-/

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.CoefficientInertia`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9a1cde9e19fd7fd9045cb8e412353c952730e33050e6479df659423d8776b955`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped TensorProduct

namespace Algebra.FiniteEtale.CoefficientInertia

variable (R K Ω H : Type*) [CommRing R] [Field K] [Algebra R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [CommRing H] [Algebra R H] [Module.Finite R H]

/-- The actual coefficient point on H_K restricts to literal integral elements. -/
def integerHom (h : (K ⊗[R] H) →ₐ[K] Ω) : H →ₐ[R] integralClosure R Ω := by
  let f : H →ₐ[R] Ω := (h.restrictScalars R).comp Algebra.TensorProduct.includeRight
  exact f.codRestrict (integralClosure R Ω) fun x =>
    (Algebra.IsIntegral.isIntegral (R := R) x).map f

@[simp] theorem integerHom_val (h : (K ⊗[R] H) →ₐ[K] Ω) (x : H) :
    (integerHom R K Ω H h x : Ω) = h ((1 : K) ⊗ₜ[R] x) := rfl

variable [Algebra.Etale R H]

/-- Literal inertia at Q fixes EVERY geometric point of the actual H_K. -/
theorem coefficients_fixed_by_absolute_inertia
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    (sigma : Ω ≃ₐ[K] Ω) (hsigma : sigma ∈ Q.inertia (Ω ≃ₐ[K] Ω))
    (h : (K ⊗[R] H) →ₐ[K] Ω) : sigma.toAlgHom.comp h = h := by
  let C := integralClosure R Ω
  let W := Localization.AtPrime Q
  let f : H →ₐ[R] C := integerHom R K Ω H h
  let g : H →ₐ[R] C := integerHom R K Ω H (sigma.toAlgHom.comp h)
  let floc : H →ₐ[R] W := (IsScalarTower.toAlgHom R C W).comp f
  let gloc : H →ₐ[R] W := (IsScalarTower.toAlgHom R C W).comp g
  have heq : gloc = floc := by
    apply Algebra.FormallyUnramified.eq_of_comp_residue_eq
    intro x
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    change algebraMap C W (g x) - algebraMap C W (f x) ∈ IsLocalRing.maximalIdeal W
    rw [← map_sub]
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff W Q _).mpr
    have hx := Ideal.mem_inertia.mp hsigma (f x)
    have hact : g x = sigma • f x := Subtype.ext rfl
    simpa only [hact] using hx
  have hpoint : ∀ x : H, sigma (h ((1 : K) ⊗ₜ[R] x)) = h ((1 : K) ⊗ₜ[R] x) := by
    intro x
    have hx : g x = f x :=
      (FaithfulSMul.algebraMap_injective C W) (DFunLike.congr_fun heq x)
    exact congrArg Subtype.val hx
  apply Algebra.TensorProduct.ext'
  intro k x
  have hleft := (sigma.toAlgHom.comp h).toLinearMap.map_smul k ((1 : K) ⊗ₜ[R] x)
  have hright := h.toLinearMap.map_smul k ((1 : K) ⊗ₜ[R] x)
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at hleft hright
  exact hleft.trans ((congrArg (fun y : Ω => k • y) (hpoint x)).trans hright.symm)

end Algebra.FiniteEtale.CoefficientInertia
