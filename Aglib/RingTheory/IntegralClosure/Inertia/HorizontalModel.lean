/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.Inertia.HorizontalAlgebra

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.ReverseModel`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`6230c7c8f079b707268d489b54c0b9c99d242cf1bdff03fee147ea33230b0822`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped TensorProduct

namespace integralClosure.Inertia.HorizontalModel

/-- The literal normalization supplies a finite etale model of the actual
generic algebra when absolute inertia acts trivially on its geometric fibre.
The generic fibre is the canonical tensor-product model. -/
theorem normalized_model
    (F R K Ω A : Type*) [Field F] [CharZero F]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra F R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [IsGalois K Ω] [IsAlgClosed Ω]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [Algebra.Etale K A]
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)]
    (htrivial : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ f : A →ₐ[K] Ω,
      σ.toAlgHom.comp f = f) :
    Module.Finite R (integralClosure R A) ∧
      Algebra.Etale R (integralClosure R A) ∧
      Nonempty (K ⊗[R] integralClosure R A ≃ₐ[K] A) := by
  haveI := Algebra.FormallyUnramified.finite_of_free K A
  exact ⟨integralClosure.finite_of_etale R K A,
    HorizontalAlgebra.model_etale_of_absolute_inertia_trivial_on_generic_fiber
      F R K Ω A Q htrivial,
    ⟨integralClosure.genericFiberEquiv R K A⟩⟩

end integralClosure.Inertia.HorizontalModel
