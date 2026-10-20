/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.Inertia.Degree
public import Aglib.RingTheory.IntegralClosure.Inertia.HorizontalNonGalois
public import Aglib.RingTheory.IntegralClosure.FiniteEtale

/-!
Supporting generalized local slice of
`K2-018#prop:k2018-arithmetic-characters` at mathematical source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`. The source's arithmetic-surface
application retains separate class/coefficient identifications and global
obligations; this module covers its explicit arbitrary-residue local conditions.

# Reverse absolute-inertia criterion with arbitrary residue fields

The exact R/K/Omega/A towers, literal prime Q and all-embedding action are
retained. NO residue perfectness, pre-assumed residue separability, field
algebra F -> R, or invertibility of a group order is used. The new degree-count
lemma derives ramification index one AND residue Galoisness from trivial finite
inertia. The rest preserves the literal normalization and canonical generic
fiber. Characteristic-zero fraction fields are included in this stronger
separable/Galois formulation.
-/

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.InertiaModel`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`228d979d9056b6bd599882df8c00874f73a9ac1eba1039ce71e1d28afffafd15`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped TensorProduct

namespace integralClosure.Inertia.FiniteEtale

open FiniteRestriction AbsoluteRestriction

variable (R K L : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The new degree-count argument derives index one together with residue
Galoisness; it does not apply the cardinality formula with separable-residue
hypotheses before those hypotheses have been derived. -/
theorem ramificationIdx_eq_one_of_inertia_eq_bot
    (P : Ideal (integralClosure R L)) [P.IsPrime]
    (hI : P.inertia (L ≃ₐ[K] L) = ⊥) : P.ramificationIdx R = 1 := by
  haveI := Horizontal.model_isGaloisGroup R K L
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  haveI : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  haveI : Module.Free R (integralClosure R L) := IsIntegralClosure.module_free R K L _
  exact (ramification_and_residue_of_inertia_eq_bot R (integralClosure R L)
    (L ≃ₐ[K] L) (P.under R) P hI).1

/-- Literal finite inertia trivial at one prime above the closed point gives
unramifiedness at every prime of the same normalization. -/
theorem model_formallyUnramified_of_inertia_eq_bot
    (P : Ideal (integralClosure R L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hI : P.inertia (L ≃ₐ[K] L) = ⊥) :
    Algebra.FormallyUnramified R (integralClosure R L) := by
  haveI := Horizontal.model_isGaloisGroup R K L
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  haveI : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  haveI : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  haveI : Module.Free R (integralClosure R L) := IsIntegralClosure.module_free R K L _
  apply Algebra.formallyUnramified_iff_forall.mpr
  intro q
  have hqI : q.asIdeal.inertia (L ≃ₐ[K] L) = ⊥ := by
    by_cases hq : q.asIdeal = ⊥
    · rw [hq]
      exact Horizontal.model_inertia_bot R K L
    · haveI : q.asIdeal.IsMaximal := q.isPrime.isMaximal hq
      haveI : q.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) :=
        ⟨(IsLocalRing.eq_maximalIdeal (inferInstance : (q.asIdeal.under R).IsMaximal)).symm⟩
      obtain ⟨sigma, hsigma⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
        (IsLocalRing.maximalIdeal R) P q.asIdeal (L ≃ₐ[K] L)
      rw [← hsigma, Ideal.inertia_smul, hI]
      simp
  haveI := hasSeparableResidueFieldsAt_of_inertia_eq_bot R (integralClosure R L)
    (L ≃ₐ[K] L) (q.asIdeal.under R) q.asIdeal hqI
  apply Ideal.ramificationIdx_eq_one_iff.mp
  exact ramificationIdx_eq_one_of_inertia_eq_bot R K L q.asIdeal hqI

/-- The finite normalization is free over the DVR, so formally unramified
implies etale for the same carrier and structural map. -/
theorem model_etale_of_inertia_eq_bot
    (P : Ideal (integralClosure R L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hI : P.inertia (L ≃ₐ[K] L) = ⊥) :
    Algebra.Etale R (integralClosure R L) := by
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  haveI : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  haveI : Module.Free R (integralClosure R L) := IsIntegralClosure.module_free R K L _
  haveI : Algebra.FinitePresentation R (integralClosure R L) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI := model_formallyUnramified_of_inertia_eq_bot R K L P hI
  exact Algebra.Etale.of_formallyUnramified_of_flat

end integralClosure.Inertia.FiniteEtale

namespace integralClosure.Inertia.Absolute

open FiniteRestriction AbsoluteRestriction

variable (R K Ω : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω]

/-- The proved restriction-surjectivity result uses the contraction of this
exact absolute prime, rather than a replacement prime or finite inertia. -/
theorem model_etale_of_absolute_inertia_fixed
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)]
    (L : FiniteGaloisIntermediateField K Ω)
    (hfixed : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ x : L, σ (x : Ω) = x) :
    Algebra.Etale R (integralClosure R L) := by
  exact FiniteEtale.model_etale_of_inertia_eq_bot R K L
    (contractedPrime R K Ω Q L)
    (HorizontalAbsolute.finite_inertia_eq_bot_of_fixed R K Ω Q L hfixed)

end integralClosure.Inertia.Absolute

namespace integralClosure.Inertia.NonGalois

open FiniteRestriction

section Tower

variable (R K L M : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Field M] [Algebra R M]
  [Algebra L M] [IsScalarTower R L M]

include K

/-- Etaleness of the normalization in an extension field descends to the
literal normalization of an arbitrary finite separable lower field. -/
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
    formallyUnramified_of_integral_tower R (integralClosure R L) (integralClosure R M)
  haveI : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  haveI : Module.Free R (integralClosure R L) := IsIntegralClosure.module_free R K L _
  haveI : Algebra.FinitePresentation R (integralClosure R L) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Tower

section Absolute

variable (R K Ω : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω]

/-- All embeddings of a finite separable field being fixed forces its normal
closure to be fixed, giving the same normalization etale without normality of
that field itself. -/
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
  have hle := HorizontalNonGalois.normalClosure_le_fixedField_of_trivial_on_generic_fiber
    R K Ω L Q htrivial
  haveI : Algebra.Etale R (integralClosure R N) :=
    Absolute.model_etale_of_absolute_inertia_fixed R K Ω Q N
      (fun σ hσ x => (IntermediateField.mem_fixedField_iff _ _).mp (hle x.property) σ hσ)
  exact model_etale_of_etale_extension R K L N

/-- An algebraically closed ambient field supplies each component embedding. -/
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
  exact model_etale_of_absolute_inertia_trivial_on_generic_fiber R K Ω L Q htrivial

end Absolute

end integralClosure.Inertia.NonGalois

namespace integralClosure.Inertia.Algebra

variable (R K Ω A : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]

/-- The normalization of a finite etale algebra, including a product of fields,
is etale when the same absolute prime's inertia fixes all geometric embeddings. -/
theorem model_etale_of_absolute_inertia_trivial_on_generic_fiber
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)]
    (htrivial : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ f : A →ₐ[K] Ω,
      σ.toAlgHom.comp f = f) :
    Algebra.Etale R (integralClosure R A) := by
  obtain ⟨ι, hι, L, hL, hKL, e, hfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  letI := hι
  letI := hL
  letI := hKL
  letI (i : ι) : Algebra R (L i) :=
    (algebraMap K (L i)).comp (algebraMap R K) |>.toAlgebra
  haveI (i : ι) : IsScalarTower R K (L i) := IsScalarTower.of_algebraMap_eq' rfl
  haveI (i : ι) : Module.Finite K (L i) := (hfin i).1
  haveI (i : ι) : Algebra.IsSeparable K (L i) := (hfin i).2
  haveI (i : ι) : Module.Finite R (integralClosure R (L i)) :=
    IsIntegralClosure.finite R K (L i) _
  haveI (i : ι) : Algebra.Etale R (integralClosure R (L i)) := by
    apply NonGalois.model_etale_of_absolute_inertia_trivial_on_all_embeddings
      R K Ω (L i) Q
    intro σ hσ f
    apply AlgHom.ext
    intro y
    obtain ⟨a, ha⟩ := ((Function.surjective_eval i).comp e.surjective) y
    have h := congrArg (fun g : A →ₐ[K] Ω => g a)
      (htrivial σ hσ (f.comp ((Pi.evalAlgHom K L i).comp e.toAlgHom)))
    change σ (f (e a i)) = f (e a i) at h
    change e a i = y at ha
    change σ (f y) = f y
    simpa only [ha] using h
  haveI : Algebra.FinitePresentation R (∀ i, integralClosure R (L i)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Etale R (∀ i, integralClosure R (L i)) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Etale.of_equiv
    (integralClosure.equivPi R A L (e.restrictScalars R)).symm


/-- Finite etaleness is obtained for literal integralClosure R A, and the
canonical tensor-product generic fiber recovers the actual algebra A. -/
theorem normalized_model
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)]
    (htrivial : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ f : A →ₐ[K] Ω,
      σ.toAlgHom.comp f = f) :
    Module.Finite R (integralClosure R A) ∧
      Algebra.Etale R (integralClosure R A) ∧
      Nonempty (K ⊗[R] integralClosure R A ≃ₐ[K] A) := by
  haveI := Algebra.FormallyUnramified.finite_of_free K A
  exact ⟨integralClosure.finite_of_etale R K A,
    model_etale_of_absolute_inertia_trivial_on_generic_fiber R K Ω A Q htrivial,
    ⟨integralClosure.genericFiberEquiv R K A⟩⟩

end integralClosure.Inertia.Algebra
