/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.MvPowerSeries.Evaluation

/-!
# Noetherianity of ideal-adic completions

A completion of a Noetherian ring is a quotient of a finite-variable power
series ring, by evaluation at the images of a finite set of ideal generators.
Neither locality nor completeness of the original ring is required.
-/

@[expose] public section

namespace AdicCompletion

universe u

/-- The ideal-adic completion of a Noetherian commutative ring is Noetherian.
This is a theorem rather than a global instance. -/
theorem isNoetherianRing (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) := by
  classical
  let S := AdicCompletion I R
  let φ : R →+* S := algebraMap R S
  let J : Ideal S := I.map φ
  have hI : I.FG := I.fg_of_isNoetherianRing
  obtain ⟨s, hs⟩ := I.fg_of_isNoetherianRing
  let : UniformSpace R := ⊥
  let : WithIdeal S := ⟨J⟩
  have hJ : IsAdic J := rfl
  have hcomplete : IsAdicComplete J S :=
    (IsAdicComplete.map_algebraMap_iff I S).mpr (AdicCompletion.isAdicComplete (M := R) hI)
  have : CompleteSpace S := hJ.isAdicComplete_iff.mp hcomplete |>.1
  have : T2Space S := hJ.isAdicComplete_iff.mp hcomplete |>.2
  let a : s → S := fun i => φ i.val
  have ha : MvPowerSeries.HasEval a := by
    constructor
    · intro i
      apply WithIdeal.isTopologicallyNilpotent_of_mem
      apply Ideal.mem_map_of_mem φ
      rw [← hs]
      exact Ideal.subset_span i.property
    · simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]
  let E : MvPowerSeries s R →+* S :=
    MvPowerSeries.eval₂Hom (φ := φ) continuous_of_discreteTopology ha
  have hE_C (r : R) : E (MvPowerSeries.C r) = φ r := by
    change MvPowerSeries.eval₂Hom _ ha (MvPowerSeries.C r) = _
    rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C]
  have hE_X (i : s) : E (MvPowerSeries.X i) = a i := by
    change MvPowerSeries.eval₂Hom _ ha (MvPowerSeries.X i) = _
    rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]
  let V : Ideal (MvPowerSeries s R) := Ideal.span (Set.range MvPowerSeries.X)
  have hmap : V.map E = J := by
    change (Ideal.span (Set.range MvPowerSeries.X)).map E = I.map φ
    rw [Ideal.map_span, ← Set.range_comp]
    have hXa : E ∘ MvPowerSeries.X = a := funext hE_X
    rw [hXa, ← congrArg (Ideal.map φ) hs, Ideal.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  have : IsHausdorff (V.map E) S := by
    rw [hmap]
    exact hcomplete.toIsHausdorff
  have hsurj : Function.Surjective E := by
    apply surjective_of_mk_map_comp_surjective E (I := V)
    change Function.Surjective ((Ideal.Quotient.mk (V.map E)).comp E)
    rw [hmap]
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalOneₐ I x)
    refine ⟨MvPowerSeries.C r, ?_⟩
    change Ideal.Quotient.mk J (E (MvPowerSeries.C r)) = Ideal.Quotient.mk J x
    rw [hE_C, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    change φ r - x ∈ I.map (algebraMap R S)
    rw [← ker_evalOneₐ_eq_map I hI]
    change evalOneₐ I (algebraMap R S r - x) = 0
    rw [map_sub, (evalOneₐ I).commutes]
    exact sub_eq_zero.mpr hr
  exact isNoetherianRing_of_surjective (MvPowerSeries s R) S E hsurj

end AdicCompletion
