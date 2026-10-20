/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.Inertia.Etale
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Algebra.CharP.IntermediateField

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.Inertia.Inseparable`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`60df82e8866d91c1118ae00c141190edf7741336668f539d038175d8f593bc3f`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

open integralClosure.Inertia.FiniteRestriction

namespace integralClosure.Inertia.Inseparable

universe u

/-- An inertia automorphism of a normal subfield lifts through a purely
inseparable ambient extension while preserving the original prime's literal
residue conditions. No separability of the ambient extension is assumed. -/
-- Retain normality of the original intermediate field S in the inertia-lifting interface; the
-- actual lift and residue calculation use ambient normality and pure inseparability.
@[nolint unusedArguments]
theorem liftNormal_mem_inertia
    (R K S Ω : Type u) [CommRing R] [Field K] [Field S] [Field Ω]
    [Algebra R K] [Algebra K S] [Algebra K Ω] [Algebra S Ω]
    [Algebra R S] [Algebra R Ω]
    [IsScalarTower R K S] [IsScalarTower R K Ω]
    [IsScalarTower K S Ω] [IsScalarTower R S Ω]
    [Normal K S] [Normal K Ω] [IsPurelyInseparable S Ω]
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    (τ : S ≃ₐ[K] S)
    (hτ : τ ∈ (Q.comap (modelMap R S Ω)).inertia (S ≃ₐ[K] S)) :
    τ.liftNormal Ω ∈ Q.inertia (Ω ≃ₐ[K] Ω) := by
  let q := ringExpChar Ω
  haveI : ExpChar Ω q := ringExpChar.expChar Ω
  haveI : ExpChar S q := (algebraMap S Ω).expChar (algebraMap S Ω).injective q
  let σ := τ.liftNormal Ω
  rw [Ideal.mem_inertia]
  intro x
  obtain ⟨n, s, hs⟩ := IsPurelyInseparable.pow_mem S q (x : Ω)
  have hsint : IsIntegral R s := by
    apply (isIntegral_algebraMap_iff (B := Ω)).mp
    rw [hs]
    exact x.property.pow (q ^ n)
  let xs : integralClosure R S := ⟨s, hsint⟩
  have hxpower : modelMap R S Ω xs = x ^ (q ^ n) := Subtype.ext hs
  have hact : modelMap R S Ω (τ • xs) = σ • modelMap R S Ω xs := by
    apply Subtype.ext
    exact (τ.liftNormal_commutes Ω s).symm
  have hres := Ideal.mem_inertia.mp hτ xs
  change modelMap R S Ω (τ • xs - xs) ∈ Q at hres
  rw [map_sub, hact, hxpower] at hres
  have hpow : (σ • x - x) ^ (q ^ n) = σ • (x ^ (q ^ n)) - x ^ (q ^ n) := by
    apply Subtype.ext
    change (σ (x : Ω) - (x : Ω)) ^ q ^ n = σ ((x : Ω) ^ q ^ n) - (x : Ω) ^ q ^ n
    rw [map_pow, sub_pow_expChar_pow]
  exact (inferInstance : Q.IsPrime).mem_of_pow_mem (q ^ n) (hpow ▸ hres)

/-- The finite-etale algebra criterion needs a separably closed Galois ambient
field; every field component is separable, so algebraic closedness is unnecessary. -/
theorem model_etale_of_sepClosed_inertia_trivial
    (R K Ω A : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [Algebra.Etale K A]
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
    let f : L i →ₐ[K] Ω := IsSepClosed.lift
    letI := f.toAlgebra
    haveI : IsScalarTower R (L i) Ω := IsScalarTower.of_algHom (f.restrictScalars R)
    apply NonGalois.model_etale_of_absolute_inertia_trivial_on_generic_fiber
      R K Ω (L i) Q
    intro σ hσ φ
    apply AlgHom.ext
    intro y
    obtain ⟨a, ha⟩ := ((Function.surjective_eval i).comp e.surjective) y
    have h := congrArg (fun g : A →ₐ[K] Ω => g a)
      (htrivial σ hσ (φ.comp ((Pi.evalAlgHom K L i).comp e.toAlgHom)))
    change σ (φ (e a i)) = φ (e a i) at h
    change e a i = y at ha
    change σ (φ y) = φ y
    simpa only [ha] using h
  haveI : Algebra.FinitePresentation R (∀ i, integralClosure R (L i)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Etale R (∀ i, integralClosure R (L i)) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Etale.of_equiv
    (integralClosure.equivPi R A L (e.restrictScalars R)).symm

/-- The reverse absolute-inertia criterion on the actual algebraic closure
works for imperfect fraction fields as well. The prime is retained through its
literal contraction to the separable closure, and every lifted automorphism
satisfies the original prime's inertia condition. -/
theorem model_etale_of_algebraicClosure_inertia_trivial
    (R K A : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [Algebra.Etale K A]
    (Q : Ideal (integralClosure R (AlgebraicClosure K))) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)]
    (htrivial : ∀ σ ∈ Q.inertia (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
      ∀ f : A →ₐ[K] AlgebraicClosure K, σ.toAlgHom.comp f = f) :
    Algebra.Etale R (integralClosure R A) := by
  let S := SeparableClosure K
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R S (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap S (AlgebraicClosure K) (algebraMap K S (algebraMap R K r)) =
        algebraMap R (AlgebraicClosure K) r
      rw [← IsScalarTower.algebraMap_apply K S (AlgebraicClosure K),
        ← IsScalarTower.algebraMap_apply R K (AlgebraicClosure K)]
  let Qs := Q.comap (modelMap R S (AlgebraicClosure K))
  haveI : Qs.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Qs.LiesOver (IsLocalRing.maximalIdeal R) := by
    constructor
    rw [Q.over_def (IsLocalRing.maximalIdeal R)]
    rfl
  apply model_etale_of_sepClosed_inertia_trivial R K S A Qs
  intro τ hτ f
  let σ := τ.liftNormal (AlgebraicClosure K)
  have hσ : σ ∈ Q.inertia (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
    liftNormal_mem_inertia R K S (AlgebraicClosure K) Q τ hτ
  have hf := htrivial σ hσ ((IsScalarTower.toAlgHom K S (AlgebraicClosure K)).comp f)
  apply AlgHom.ext
  intro a
  apply (algebraMap S (AlgebraicClosure K)).injective
  calc
    algebraMap S (AlgebraicClosure K) (τ (f a)) =
        σ (algebraMap S (AlgebraicClosure K) (f a)) :=
      (τ.liftNormal_commutes (AlgebraicClosure K) (f a)).symm
    _ = algebraMap S (AlgebraicClosure K) (f a) :=
      congrArg (fun g : A →ₐ[K] AlgebraicClosure K => g a) hf

end integralClosure.Inertia.Inseparable
