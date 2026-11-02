/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.CompleteLocalEvaluation
public import Aglib.RingTheory.LocalRing.CoefficientSection
public import Aglib.RingTheory.RegularLocalRing.RegularSequence

/-!
# Original formal coordinates in regular characteristic-p dimension-two rings

The existing residue coefficient section and an actual two-element regular
system of parameters identify the original complete ring with native formal
series. The same evaluation retains constants, variables and residue values.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace IsRegularLocalRing

variable (R : Type*) [CommRing R] [IsRegularLocalRing R]

/-- Two original minimal parameters, not merely a maximal-radical parameter ideal. -/
theorem exists_two_generators_maximalIdeal (hdim : ringKrullDim R = 2) :
    ∃ x : Fin 2 → R, Ideal.span (Set.range x) = maximalIdeal R := by
  obtain ⟨rs, hlen, -, hspan⟩ := exists_regular_sequence_maximalIdeal R 2 hdim
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  refine ⟨![a, b], ?_⟩
  have hrange : Set.range (![a, b] : Fin 2 → R) = {a, b} := by
    ext c
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [hrange]
  simpa only [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq,
    ← Ideal.span_insert] using hspan

variable [IsAdicComplete (maximalIdeal R) R]

/-- Complete regular characteristic-p dimension-two rings admit actual formal
coordinates over their native residue field. The coefficient map is the existing
chosen section, not a new arbitrary section premise. -/
theorem exists_formalCoordinatesTwo_of_charP
    (p : ℕ) [Fact p.Prime] [CharP R p] (hdim : ringKrullDim R = 2) :
    ∃ x : Fin 2 → R, ∃ e : MvPowerSeries (Fin 2) (ResidueField R) ≃+* R,
      Ideal.span (Set.range x) = maximalIdeal R ∧
      (∀ c, e (MvPowerSeries.C c) = coefficientSectionOfCharP R p c) ∧
      (∀ i, e (MvPowerSeries.X i) = x i) ∧
      (∀ f, residue R (e f) = MvPowerSeries.constantCoeff f) := by
  obtain ⟨x, hspan⟩ := exists_two_generators_maximalIdeal R hdim
  have hx (i : Fin 2) : x i ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hres : Function.Surjective ((residue R).comp (coefficientSectionOfCharP R p)) := by
    intro c
    exact ⟨c, residue_coefficientSectionOfCharP R p c⟩
  let e := MvPowerSeries.completeLocalEquivTwo
    (coefficientSectionOfCharP R p) x hx hspan hres hdim
  refine ⟨x, e, hspan,
    MvPowerSeries.completeLocalEquivTwo_C _ _ _ _ _ _,
    MvPowerSeries.completeLocalEquivTwo_X _ _ _ _ _ _, ?_⟩
  intro f
  exact (MvPowerSeries.residue_completeLocalEval _ x hx f).trans
    (residue_coefficientSectionOfCharP R p _)

end IsRegularLocalRing
