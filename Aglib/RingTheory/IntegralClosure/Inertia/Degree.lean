/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Smooth.Fiber

/-!
Supporting generalized local slice of
`K2-018#prop:k2018-arithmetic-characters` at mathematical source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`. The source's arithmetic-surface
application retains separate class/coefficient identifications and global
obligations; this module covers its explicit arbitrary-residue local conditions.

# Trivial literal inertia forces residue separability

The degree identity and orbit-stabilizer count below require finite flat domains
and a finite Galois ring action, but no residue separability or perfectness.
The residue automorphism map is independently surjective. When its kernel
(the literal inertia) is trivial, card Aut = e*f; card Aut <= f forces e=1 and
card Aut=f, hence a Galois residue extension. This is the non-circular input
needed to remove perfect residue from the DVR normalization criterion.
-/
/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.Inertia.Degree`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`5e58f9e2a1d61a63871adc952c19630ab2aa961775e09957a45386ea267eddf1`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace integralClosure.Inertia.FiniteEtale

open scoped Pointwise

variable (R S G : Type*) [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S] [Algebra R S]
  [Module.Finite R S] [Module.Flat R S]
  [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
  (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]

include p in
theorem card_stabilizer_eq_ramification_mul_inertiaDeg :
    Nat.card (MulAction.stabilizer G P) = P.ramificationIdx R * P.inertiaDeg R := by
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G,
    Ideal.inertiaDegIn_eq_inertiaDeg p P G] at hfund
  have horbit : (p.primesOver S).ncard * Nat.card (MulAction.stabilizer G P) = Nat.card G := by
    rw [← Algebra.IsInvariant.orbit_eq_primesOver R S G p P]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hn : (p.primesOver S).ncard ≠ 0 := by grind [Nat.card_pos]
  exact (mul_right_inj' hn).mp (horbit.trans hfund.symm)


/-- Trivial inertia forces BOTH index one and Galois residue, with no
pre-assumed residue separability or perfectness. -/
theorem ramification_and_residue_of_inertia_eq_bot
    (hI : P.inertia G = ⊥) :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    P.ramificationIdx R = 1 ∧ IsGalois p.ResidueField P.ResidueField := by
  letI := Localization.AtPrime.algebraOfLiesOver p P
  haveI : Module.Finite p.ResidueField P.ResidueField := inferInstance
  have heq : (algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P)) =
      (algebraMap p.ResidueField P.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  letI := ((algebraMap (S ⧸ P) P.ResidueField).comp
    (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  haveI : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField := .of_algebraMap_eq' rfl
  haveI : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField := .of_algebraMap_eq' heq
  let D := MulAction.stabilizer G P
  let rho : D →* (P.ResidueField ≃ₐ[p.ResidueField] P.ResidueField) :=
    IsFractionRing.stabilizerHom G p P p.ResidueField P.ResidueField
  have hker : rho.ker = ⊥ := by
    change (IsFractionRing.stabilizerHom G p P p.ResidueField P.ResidueField).ker = ⊥
    rw [IsFractionRing.ker_stabilizerHom]
    change (P.inertia G).subgroupOf D = ⊥
    rw [hI]
    simp
  have hrho : Function.Bijective rho :=
    ⟨(MonoidHom.ker_eq_bot_iff rho).mp hker,
      IsFractionRing.stabilizerHom_surjective G p P p.ResidueField P.ResidueField⟩
  let e := MulEquiv.ofBijective rho hrho
  have hcard : Nat.card (P.ResidueField ≃ₐ[p.ResidueField] P.ResidueField) =
      P.ramificationIdx R * P.inertiaDeg R :=
    (Nat.card_congr e.toEquiv).symm.trans
      (card_stabilizer_eq_ramification_mul_inertiaDeg R S G p P)
  have hbound : Nat.card (P.ResidueField ≃ₐ[p.ResidueField] P.ResidueField) ≤
      P.inertiaDeg R := by
    rw [Ideal.inertiaDeg_eq p P]
    simpa only [Nat.card_eq_fintype_card] using
      (AlgEquiv.card_le (F := p.ResidueField) (K := P.ResidueField))
  have hepos : 0 < P.ramificationIdx R := P.ramificationIdx_pos R
  have hfpos : 0 < P.inertiaDeg R := P.inertiaDeg_pos R
  have he : P.ramificationIdx R = 1 := by nlinarith [hcard]
  refine ⟨he, IsGalois.of_card_aut_eq_finrank p.ResidueField P.ResidueField ?_⟩
  rw [he, one_mul, Ideal.inertiaDeg_eq p P] at hcard
  exact hcard


/-- Separability at every prime over p follows by Galois conjugacy of the
literal inertia group and the newly derived residue Galois condition. -/
theorem hasSeparableResidueFieldsAt_of_inertia_eq_bot
    (hI : P.inertia G = ⊥) : Algebra.HasSeparableResidueFieldsAt R S p := by
  constructor
  intro Q _ _
  letI := Localization.AtPrime.algebraOfLiesOver p Q
  obtain ⟨sigma, hsigma⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p P Q G
  have hQI : Q.inertia G = ⊥ := by
    rw [← hsigma, Ideal.inertia_smul, hI]
    simp
  haveI : IsGalois p.ResidueField Q.ResidueField :=
    (ramification_and_residue_of_inertia_eq_bot R S G p Q hQI).2
  infer_instance

end integralClosure.Inertia.FiniteEtale


namespace integralClosure.Inertia.NonGalois

/-- General descent: the upper unramified algebra supplies residue separability,
which passes down the injective integral tower. No perfectness is required. -/
theorem formallyUnramified_of_integral_tower
    (R S T : Type*) [CommRing R]
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
  haveI : Algebra.HasSeparableResidueFieldsAt R T (q.asIdeal.under R) := by
    constructor
    intro t _ _
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) t
    infer_instance
  haveI := Algebra.HasSeparableResidueFieldsAt.tower_bot
    (A := R) (B := S) (C := T) (q.asIdeal.under R)
  apply Ideal.ramificationIdx_eq_one_iff.mp
  apply Nat.dvd_one.mp
  rw [← r.ramificationIdx_eq_one R]
  exact q.asIdeal.ramificationIdx_below_dvd r

end integralClosure.Inertia.NonGalois
