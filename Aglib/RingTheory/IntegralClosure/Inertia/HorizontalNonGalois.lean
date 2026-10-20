/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.Inertia.HorizontalAbsolute

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.NonGaloisEtale`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b6cb784ff8835fcd85c9867e1cc9c3dee69b8017b12cf6bebf53271329eb70b9`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace integralClosure.Inertia.HorizontalNonGalois

open FiniteRestriction

/-- Over a characteristic-zero field algebra, unramifiedness descends through
an injective integral extension from a Dedekind domain. Ramification indices
divide those upstairs, and all residue extensions are separable. -/
theorem formallyUnramified_of_integral_tower
    (F R S T : Type*) [Field F] [CharZero F]
    [CommRing R] [Algebra F R]
    [CommRing S] [IsDedekindDomain S]
    [CommRing T] [IsDomain T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [FaithfulSMul S T] [Algebra.IsIntegral S T]
    [Module.Finite R S] [Algebra.EssFiniteType R T]
    [Algebra.FormallyUnramified R T] : Algebra.FormallyUnramified R S := by
  apply Algebra.formallyUnramified_iff_forall.mpr
  intro q
  obtain ⟨r, hr, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := T) q.asIdeal (by
      simp [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective S T)])
  letI : r.IsPrime := hr
  letI : r.LiesOver q.asIdeal := ⟨hc.symm⟩
  haveI : CharZero (q.asIdeal.under R).ResidueField :=
    Horizontal.residueField_charZero F R _
  apply Ideal.ramificationIdx_eq_one_iff.mp
  apply Nat.dvd_one.mp
  rw [← r.ramificationIdx_eq_one R]
  exact q.asIdeal.ramificationIdx_below_dvd r

section Tower

variable (F R K L M : Type*) [Field F] [CharZero F]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra F R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Field M] [Algebra R M]
  [Algebra L M] [IsScalarTower R L M]

include F K

/-- An etale normalization in an extension field forces the literal lower
normalization to be etale. The finite lower field need not be Galois. -/
theorem model_etale_of_etale_extension
    [Algebra.Etale R (integralClosure R M)] :
    Algebra.Etale R (integralClosure R L) := by
  letI := (modelMap R L M).toAlgebra
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  haveI : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  haveI : FaithfulSMul (integralClosure R L) (integralClosure R M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      intro x y h
      apply Subtype.ext
      apply (algebraMap L M).injective
      exact congrArg Subtype.val h)
  haveI : Algebra.IsIntegral (integralClosure R L) (integralClosure R M) :=
    Algebra.IsIntegral.tower_top (R := R)
  haveI : Algebra.FormallyUnramified R (integralClosure R L) :=
    formallyUnramified_of_integral_tower F R (integralClosure R L) (integralClosure R M)
  haveI : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  haveI : Module.Free R (integralClosure R L) := IsIntegralClosure.module_free R K L _
  haveI : Algebra.FinitePresentation R (integralClosure R L) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Tower

section Absolute

variable (R K Ω : Type*) [CommRing R] [Field K] [Field Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω]

omit [IsGalois K Ω] in
/-- Trivial inertia on every embedding of a finite separable field fixes every
conjugate and hence its actual normal closure inside the ambient Galois field. -/
theorem normalClosure_le_fixedField_of_trivial_on_generic_fiber
    (L : Type*) [Field L] [Algebra K L]
    (Q : Ideal (integralClosure R Ω))
    (htrivial : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ f : L →ₐ[K] Ω,
      σ.toAlgHom.comp f = f) :
    IntermediateField.normalClosure K L Ω ≤
      IntermediateField.fixedField (Q.inertia (Ω ≃ₐ[K] Ω)) := by
  apply normalClosure_le_iff.mpr
  intro f x hx
  obtain ⟨y, rfl⟩ := hx
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  exact congrArg (fun g : L →ₐ[K] Ω => g y) (htrivial σ hσ f)

variable (F : Type*) [Field F] [CharZero F] [Algebra F R]
  [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

include F

/-- Reverse inertia criterion for an arbitrary finite separable field embedded
in the ambient Galois field. The field component itself need not be Galois. -/
theorem model_etale_of_absolute_inertia_trivial_on_generic_fiber
    (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra L Ω] [IsScalarTower K L Ω] [IsScalarTower R L Ω]
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)]
    (htrivial : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ f : L →ₐ[K] Ω,
      σ.toAlgHom.comp f = f) :
    Algebra.Etale R (integralClosure R L) := by
  let N : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := IntermediateField.normalClosure K L Ω }
  haveI : IsScalarTower R N Ω := AbsoluteRestriction.subfieldAmbientTower R K Ω N
  letI : Algebra L N := normalClosure.algebra K L Ω
  haveI : IsScalarTower L N Ω := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R L N := IsScalarTower.of_algebraMap_eq fun r => by
    apply (algebraMap N Ω).injective
    rw [← IsScalarTower.algebraMap_apply R N Ω,
      ← IsScalarTower.algebraMap_apply L N Ω,
      ← IsScalarTower.algebraMap_apply R L Ω]
  have hle := normalClosure_le_fixedField_of_trivial_on_generic_fiber R K Ω L Q htrivial
  haveI : Algebra.Etale R (integralClosure R N) :=
    HorizontalAbsolute.model_etale_of_absolute_inertia_fixed R K Ω F Q N
      (fun σ hσ x => (IntermediateField.mem_fixedField_iff _ _).mp (hle x.property) σ hσ)
  exact model_etale_of_etale_extension F R K L N

/-- Over an algebraically closed ambient Galois field, the component needs no
chosen embedding or normality hypothesis. -/
theorem model_etale_of_absolute_inertia_trivial_on_all_embeddings
    [IsAlgClosed Ω]
    (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)]
    (htrivial : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ f : L →ₐ[K] Ω,
      σ.toAlgHom.comp f = f) :
    Algebra.Etale R (integralClosure R L) := by
  let f : L →ₐ[K] Ω := IsAlgClosed.lift
  letI := f.toAlgebra
  haveI : IsScalarTower R L Ω := IsScalarTower.of_algHom (f.restrictScalars R)
  exact model_etale_of_absolute_inertia_trivial_on_generic_fiber R K Ω F L Q htrivial

end Absolute

end integralClosure.Inertia.HorizontalNonGalois
