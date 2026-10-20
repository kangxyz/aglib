/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Unramified.Rigidity
public import Aglib.RingTheory.IntegralClosure.Inertia
public import Mathlib.RingTheory.Etale.Basic

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.InertiaEtaleAlgebra`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3471e56a30fd8c90b95c99ff4fe8c04f108c9b65ba22086306a96e640b6d3101`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
namespace integralClosure.Inertia

/-- View the actual Galois element as the underlying algebra automorphism. -/
abbrev galoisAutomorphism {K : Type*} [Field K] (γ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := γ

variable {R K A : Type*} [CommRing R] [Field K] [Algebra R K]
  [CommRing A] [Algebra R A] [Module.Finite R A]

/-- A point of a finite algebra in the algebraic closure factors through the
actual integral closure of the base. -/
def integralPoint (f : A →ₐ[R] AlgebraicClosure K) : A →ₐ[R] IntegralModel R K :=
  f.codRestrict (integralClosure R (AlgebraicClosure K))
    (fun a => (Algebra.IsIntegral.isIntegral a).map f)

@[simp] theorem integralPoint_val (f : A →ₐ[R] AlgebraicClosure K) (a : A) :
    (integralPoint f a).val = f a := rfl

/-- Actual integral-closure inertia fixes every algebraic point of a finite
étale algebra. This uses the defining residue-triviality and unramified
rigidity; it assumes no DVR or Noetherian structure on the integral closure. -/
theorem inertia_fixes_algHom [Algebra.Etale R A] (Q : Ideal (IntegralModel R K)) [Q.IsPrime]
    (γ : inertia R K Q) (f : A →ₐ[R] AlgebraicClosure K) (a : A) :
    galoisAutomorphism γ.val (f a) = f a := by
  let g : A →ₐ[R] AlgebraicClosure K :=
    ((galoisAutomorphism γ.val).restrictScalars R).toAlgHom.comp f
  have he : integralPoint g = integralPoint f :=
    Algebra.FormallyUnramified.eq_of_comp_mkQ_eq Q
      (integralPoint g) (integralPoint f) (fun b => by
        apply Ideal.Quotient.eq.mpr
        exact (mem_inertia_iff R K Q γ.val).mp γ.property (integralPoint f b))
  exact congrArg Subtype.val (congrArg (fun h : A →ₐ[R] IntegralModel R K => h a) he)

end integralClosure.Inertia
