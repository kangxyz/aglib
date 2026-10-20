/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Smooth.Fiber

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.HorizontalEtale`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`26235359a435009b268bf1a2893755cf8bfc79e477ce38404c6fb7e8297d7ef8`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace integralClosure.Inertia.Horizontal

/-- A residue field of an algebra over a characteristic-zero field has
characteristic zero via the actual composite field homomorphism. -/
theorem residueField_charZero (F R : Type*) [Field F] [CharZero F]
    [CommRing R] [Algebra F R] (p : Ideal R) [p.IsPrime] :
    CharZero p.ResidueField := by
  let f : F →+* p.ResidueField := (algebraMap R p.ResidueField).comp (algebraMap F R)
  exact charZero_of_injective_ringHom f.injective

variable (F R K L : Type*) [Field F] [CharZero F]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra F R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The native Galois action on the actual integral closure is a Galois ring
extension. Its action is the literal restriction of field automorphisms. -/
theorem model_isGaloisGroup :
    IsGaloisGroup (L ≃ₐ[K] L) R (integralClosure R L) := by
  haveI : IsFractionRing (integralClosure R L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R K L _
  exact IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) R (integralClosure R L) K L

/-- Faithfulness makes the inertia group at the zero prime trivial. -/
theorem model_inertia_bot :
    (⊥ : Ideal (integralClosure R L)).inertia (L ≃ₐ[K] L) = ⊥ := by
  haveI := model_isGaloisGroup R K L
  haveI := (inferInstance : IsGaloisGroup (L ≃ₐ[K] L) R (integralClosure R L)).faithful
  apply bot_unique
  intro σ hσ
  rw [Subgroup.mem_bot]
  exact eq_of_smul_eq_smul (fun x : integralClosure R L => by
    simpa only [Ideal.mem_bot, sub_eq_zero, one_smul] using (Ideal.mem_inertia.mp hσ x))

include F

/-- On the horizontal trait, the cardinality formula gives ramification index
one from trivial literal finite inertia. No residue-characteristic hypothesis
is inferred from `CharZero R`. -/
theorem ramificationIdx_eq_one_of_inertia_eq_bot
    (P : Ideal (integralClosure R L)) [P.IsPrime]
    (hI : P.inertia (L ≃ₐ[K] L) = ⊥) : P.ramificationIdx R = 1 := by
  haveI := model_isGaloisGroup R K L
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  haveI : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  haveI : Module.Free R (integralClosure R L) := IsIntegralClosure.module_free R K L _
  haveI : CharZero (P.under R).ResidueField := residueField_charZero F R (P.under R)
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.under R) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under R) P (L ≃ₐ[K] L), hI] at hcard
  simpa using hcard.symm

/-- Trivial inertia at one prime above the closed point forces the actual
normalization to be unramified everywhere. Nonzero primes are maximal, and
Galois conjugacy gives the same ramification index above the closed point. -/
theorem model_formallyUnramified_of_inertia_eq_bot
    (P : Ideal (integralClosure R L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hI : P.inertia (L ≃ₐ[K] L) = ⊥) :
    Algebra.FormallyUnramified R (integralClosure R L) := by
  haveI := model_isGaloisGroup R K L
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  haveI : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  have hP := ramificationIdx_eq_one_of_inertia_eq_bot F R K L P hI
  apply Algebra.formallyUnramified_iff_forall.mpr
  intro q
  haveI : CharZero (q.asIdeal.under R).ResidueField := residueField_charZero F R _
  apply Ideal.ramificationIdx_eq_one_iff.mp
  by_cases hq : q.asIdeal = ⊥
  · apply ramificationIdx_eq_one_of_inertia_eq_bot F R K L q.asIdeal
    rw [hq]
    exact model_inertia_bot R K L
  · haveI : q.asIdeal.IsMaximal := q.isPrime.isMaximal hq
    haveI : q.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) :=
      ⟨(IsLocalRing.eq_maximalIdeal (inferInstance : (q.asIdeal.under R).IsMaximal)).symm⟩
    exact (Ideal.ramificationIdx_eq_of_isGaloisGroup
      (IsLocalRing.maximalIdeal R) q.asIdeal P (L ≃ₐ[K] L)).trans hP

/-- The actual finite normalization is etale once literal inertia is trivial
at one prime over the closed point of the horizontal DVR. -/
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
  haveI := model_formallyUnramified_of_inertia_eq_bot F R K L P hI
  exact Algebra.Etale.of_formallyUnramified_of_flat

end integralClosure.Inertia.Horizontal
