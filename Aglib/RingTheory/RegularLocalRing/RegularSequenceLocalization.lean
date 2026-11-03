/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Regular.SequenceLocalization
public import Aglib.RingTheory.RegularLocalRing.RegularSequence

/-!
# Exact prime-ideal parameters on a principal neighbourhood

Parameters of the original regular prime localization lift with their length
retained. Over a Noetherian ring, one principal neighbourhood makes the lifted
list regular and makes its ideal equal to the extension of the original prime.
Dimension two is a thin regular-pair specialization of the same construction.
-/

@[expose] public noncomputable section

universe u

open RingTheory.Sequence
open scoped Pointwise

namespace IsRegularLocalRing

/-- Lift the original local parameters, retaining their length and exact localized ideal. -/
theorem exists_regular_generators_atPrime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime p)]
    (d : ℕ) (hd : ringKrullDim (Localization.AtPrime p) = (d : ℕ)) :
    ∃ rs : List R, rs.length = d ∧
      IsWeaklyRegular (Localization.AtPrime p) (rs.map (algebraMap R (Localization.AtPrime p))) ∧
      (Ideal.ofList rs).map (algebraMap R (Localization.AtPrime p)) =
        p.map (algebraMap R (Localization.AtPrime p)) := by
  obtain ⟨rs, hlen, hreg, hgen⟩ :=
    exists_regular_sequence_maximalIdeal (Localization.AtPrime p) d hd
  obtain ⟨ts, hlen', ht, hI⟩ := exists_integer_weaklyRegular_list p.primeCompl
    (Localization.AtPrime p) rs hreg.toIsWeaklyRegular
  refine ⟨ts, hlen'.trans hlen, ht, ?_⟩
  simpa only [hgen, Localization.AtPrime.map_eq_maximalIdeal] using hI

/-- The same lifted parameters are regular and generate the exact prime on one principal open. -/
theorem exists_regular_sequence_away
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime p)]
    (d : ℕ) (hd : ringKrullDim (Localization.AtPrime p) = (d : ℕ)) :
    ∃ rs : List R, rs.length = d ∧ ∃ f ∉ p,
      IsWeaklyRegular (Localization.Away f)
        (rs.map (algebraMap R (Localization.Away f))) ∧
      Ideal.ofList (rs.map (algebraMap R (Localization.Away f))) =
        p.map (algebraMap R (Localization.Away f)) := by
  obtain ⟨rs, hlen, hseq, hgen⟩ := exists_regular_generators_atPrime p d hd
  let I := Ideal.ofList rs
  have hIp : I ≤ p := by
    have hle := Ideal.le_comap_map (f := algebraMap R (Localization.AtPrime p)) (I := I)
    have heq : (p.map (algebraMap R (Localization.AtPrime p))).comap
        (algebraMap R (Localization.AtPrime p)) = p :=
      Ideal.under_map_of_isLocalizationAtPrime p le_rfl
    rw [hgen, heq] at hle
    exact hle
  obtain ⟨g, hg, hclear⟩ := exists_notMem_mul_mem_prefix_of_atPrime p rs
    (fun i => Ideal.fg_of_isNoetherianRing
      (Submodule.comap (LinearMap.mulLeft R rs[i]) (Ideal.ofList (rs.take i)))) hseq
  obtain ⟨c, hc, hmul⟩ :=
    Ideal.exists_mul_mem_of_map_le_atPrime p p I p.fg_of_isNoetherianRing hgen.ge
  let f := g * c
  have hf : f ∉ p := p.primeCompl.mul_mem hg hc
  refine ⟨rs, hlen, f, hf, ?_, ?_⟩
  · apply isWeaklyRegular_of_mul_mem_prefix (Submonoid.powers f) (Localization.Away f)
      rs ⟨f, Submonoid.mem_powers f⟩
    intro i x hx
    simpa only [f, mul_assoc, mul_comm, mul_left_comm] using
      (Ideal.ofList (rs.take i)).mul_mem_left c (hclear i x hx)
  · rw [← Ideal.map_ofList]
    apply le_antisymm (Ideal.map_mono hIp)
    apply Ideal.map_le_away_of_mul_mem
    intro x hx
    simpa only [f, mul_assoc] using I.mul_mem_left g (hmul x hx)

/-- A two-dimensional regular prime has an actual regular-pair neighbourhood of its exact ideal. -/
theorem exists_regularPair_away
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime p)]
    (hd : ringKrullDim (Localization.AtPrime p) = 2) :
    ∃ f ∉ p, ∃ a b : Localization.Away f,
      Ideal.span {a, b} = p.map (algebraMap R (Localization.Away f)) ∧
      IsSMulRegular (Localization.Away f) a ∧
      IsSMulRegular (Localization.Away f ⧸ Ideal.span {a}) b := by
  obtain ⟨rs, hlen, f, hf, hreg, hgen⟩ := exists_regular_sequence_away p 2 hd
  obtain ⟨r, s, rfl⟩ := List.length_eq_two.mp hlen
  let S := Localization.Away f
  let a : S := algebraMap R S r
  let b : S := algebraMap R S s
  have hpair : IsWeaklyRegular S [a, b] := by
    simpa only [List.map_cons, List.map_nil] using hreg
  have hfirst := (isWeaklyRegular_cons_iff S a [b]).mp hpair
  have hsecond := (isWeaklyRegular_cons_iff (QuotSMulTop a S) b []).mp hfirst.2
  have hquot : a • (⊤ : Submodule S S) = Ideal.span {a} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop a S ≃ₗ[S] S ⧸ Ideal.span {a} :=
    Submodule.quotEquivOfEq _ _ hquot
  refine ⟨f, hf, a, b, ?_, hfirst.1, (e.isSMulRegular_congr b).mp hsecond.1⟩
  change Ideal.ofList [a, b] = p.map (algebraMap R S) at hgen
  simpa only [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq, Ideal.span_insert] using hgen

end IsRegularLocalRing
