/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.Inertia.Absolute
public import Aglib.RingTheory.IntegralClosure.Inertia.Horizontal

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.GaloisEtale`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3144c7614d5d33d5f79224d2134f7ff3fd3ca9d47e6197c7e28f6fabdb7ed46e`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace integralClosure.Inertia.HorizontalAbsolute

open AbsoluteRestriction FiniteRestriction

variable (R K Ω : Type*) [CommRing R] [Field K] [Field Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω]

/-- Contraction retains the same base prime. -/
instance contractedPrime_liesOver (p : Ideal R)
    (Q : Ideal (integralClosure R Ω)) [Q.LiesOver p]
    (L : FiniteGaloisIntermediateField K Ω) :
    (contractedPrime R K Ω Q L).LiesOver p := by
  constructor
  rw [Q.over_def p]
  rfl

/-- Pointwise triviality of actual absolute inertia on the finite Galois
subfield kills its finite inertia, using the proved surjectivity. -/
theorem finite_inertia_eq_bot_of_fixed
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    (L : FiniteGaloisIntermediateField K Ω)
    (hfixed : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ x : L, σ (x : Ω) = x) :
    (contractedPrime R K Ω Q L).inertia (L ≃ₐ[K] L) = ⊥ := by
  rw [← AbsoluteRestriction.map_inertia_eq R K Ω Q L]
  apply bot_unique
  rintro τ ⟨σ, hσ, rfl⟩
  rw [Subgroup.mem_bot]
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact (AlgEquiv.restrictNormalHom_apply L.toIntermediateField σ x).trans (hfixed σ hσ x)

omit [IsGalois K Ω] in
/-- The literal action on the geometric generic fibre implies the pointwise
fixed-field condition, by evaluating at the given inclusion. -/
theorem fixed_of_trivial_on_generic_fiber
    (Q : Ideal (integralClosure R Ω))
    (L : FiniteGaloisIntermediateField K Ω)
    (htrivial : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ f : L →ₐ[K] Ω,
      σ.toAlgHom.comp f = f) :
    ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ x : L, σ (x : Ω) = x := by
  intro σ hσ x
  exact congrArg (fun f : L →ₐ[K] Ω => f x)
    (htrivial σ hσ (IntermediateField.val L.toIntermediateField))

variable (F : Type*) [Field F] [CharZero F] [Algebra F R]
  [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

include F

/-- Actual absolute inertia fixing a finite Galois subfield forces the same
integral closure to be etale over the horizontal DVR. -/
theorem model_etale_of_absolute_inertia_fixed
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)]
    (L : FiniteGaloisIntermediateField K Ω)
    (hfixed : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ x : L, σ (x : Ω) = x) :
    Algebra.Etale R (integralClosure R L) := by
  exact Horizontal.model_etale_of_inertia_eq_bot F R K L
    (contractedPrime R K Ω Q L) (finite_inertia_eq_bot_of_fixed R K Ω Q L hfixed)

/-- Reverse criterion for the actual geometric generic fibre of a finite
Galois subextension and its literal normalization. -/
theorem model_etale_of_absolute_inertia_trivial_on_generic_fiber
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)]
    (L : FiniteGaloisIntermediateField K Ω)
    (htrivial : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ f : L →ₐ[K] Ω,
      σ.toAlgHom.comp f = f) :
    Algebra.Etale R (integralClosure R L) := by
  exact model_etale_of_absolute_inertia_fixed R K Ω F Q L
    (fixed_of_trivial_on_generic_fiber R K Ω Q L htrivial)

end integralClosure.Inertia.HorizontalAbsolute
