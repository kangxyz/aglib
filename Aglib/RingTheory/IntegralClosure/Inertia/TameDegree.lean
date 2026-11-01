/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.SeparableDegree.Invertible
public import Aglib.RingTheory.IntegralClosure.Inertia.Degree

/-! # Actual ramification and residue degrees at prime-to-order Galois primes

The original decomposition-group cardinal is the product of ramification and
residue degrees, without a separability hypothesis. Both degrees divide the
original finite group order. If that order is invertible in the base residue
field, the actual residue extension is separable and the ramification index
is invertible there. The chosen prime need not be fixed by the whole group.
This does not construct a tame Kummer chart or an Abhyankar normalization.
-/

@[expose] public noncomputable section

open scoped Pointwise

namespace integralClosure.Inertia.FiniteEtale

universe r s g

variable (R : Type r) (S : Type s) (G : Type g)
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
  [Module.Finite R S] [Module.Flat R S]
  [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
  (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]

include p

/-- The actual ramification index divides the order of the original Galois group. -/
theorem ramificationIdx_dvd_card : P.ramificationIdx R ∣ Nat.card G := by
  have hd : P.ramificationIdx R ∣ Nat.card (MulAction.stabilizer G P) := by
    rw [card_stabilizer_eq_ramification_mul_inertiaDeg R S G p P]
    exact ⟨P.inertiaDeg R, rfl⟩
  exact hd.trans (MulAction.stabilizer G P).card_subgroup_dvd_card

/-- The actual residue degree divides the order of the original Galois group,
without pre-assuming residue separability. -/
theorem inertiaDeg_dvd_card : P.inertiaDeg R ∣ Nat.card G := by
  have hd : P.inertiaDeg R ∣ Nat.card (MulAction.stabilizer G P) := by
    rw [card_stabilizer_eq_ramification_mul_inertiaDeg R S G p P]
    exact ⟨P.ramificationIdx R, mul_comm _ _⟩
  exact hd.trans (MulAction.stabilizer G P).card_subgroup_dvd_card

/-- Invertibility of the original group order gives invertibility of the
unchanged ramification index in the actual base residue field. -/
theorem ramificationIdx_isUnit (hG : IsUnit (Nat.card G : p.ResidueField)) :
    IsUnit (P.ramificationIdx R : p.ResidueField) := by
  apply isUnit_of_dvd_unit _ hG
  obtain ⟨d, hd⟩ := ramificationIdx_dvd_card R S G p P
  exact ⟨(d : p.ResidueField), by rw [hd, Nat.cast_mul]⟩

/-- The original chosen-prime residue extension is separable by its actual
finite degree. No perfect fraction field or residue-separability premise is added. -/
theorem residue_isSeparable_of_isUnit_card (hG : IsUnit (Nat.card G : p.ResidueField)) :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    Algebra.IsSeparable p.ResidueField P.ResidueField := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  apply Field.isSeparable_of_isUnit_finrank
  have hu : IsUnit (P.inertiaDeg R : p.ResidueField) := by
    apply isUnit_of_dvd_unit _ hG
    obtain ⟨d, hd⟩ := inertiaDeg_dvd_card R S G p P
    exact ⟨(d : p.ResidueField), by rw [hd, Nat.cast_mul]⟩
  rw [Ideal.inertiaDeg_eq p P] at hu
  exact hu

/-- The same original order hypothesis supplies separable residue fields at
all primes over the chosen base prime, not just a selected local factor. -/
theorem hasSeparableResidueFieldsAt_of_isUnit_card
    (hG : IsUnit (Nat.card G : p.ResidueField)) :
    Algebra.HasSeparableResidueFieldsAt R S p := by
  constructor
  intro Q _ _
  exact residue_isSeparable_of_isUnit_card R S G p Q hG

end integralClosure.Inertia.FiniteEtale
