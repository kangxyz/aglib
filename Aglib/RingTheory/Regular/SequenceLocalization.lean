/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.IdealSpreading
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Data.List.OfFn

/-!
# Regular sequences on original localizations

Finite colon ideals supply one common clearing element for a regular sequence
at a prime. The same bounds prove regularity in any specified localization
inverting that element. Common-denominator lifting retains the length and exact
ideal of the original localized list. These mechanisms are extracted from the
private regular-sequence suppliers in `Excellent.J2Criterion`.
-/

@[expose] public noncomputable section

universe u v

open RingTheory.Sequence
open scoped Pointwise

namespace IsLocalization

/-- A cleared colon gives quotient regularity in the specified original localization. -/
theorem isSMulRegular_quotient_of_mul_mem
    {R : Type u} [CommRing R] (M : Submonoid R) (S : Type v) [CommRing S]
    [Algebra R S] [IsLocalization M S] (I : Ideal R) (a : R) (g : M)
    (hclear : ∀ x : R, a * x ∈ I → (g : R) * x ∈ I) :
    IsSMulRegular (S ⧸ I.map (algebraMap R S)) (algebraMap R S a) := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
  intro z hz
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M z
  change algebraMap R S a * IsLocalization.mk' _ x s ∈ _ at hz
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul] at hz
  obtain ⟨t, ht, htx⟩ :=
    (IsLocalization.mk'_mem_map_algebraMap_iff M S I (a * x) s).mp hz
  have hatx : a * (t * x) ∈ I := by
    simpa only [mul_left_comm] using htx
  apply (IsLocalization.mk'_mem_map_algebraMap_iff M S I x s).mpr
  exact ⟨(g : R) * t, M.mul_mem g.property ht,
    by simpa only [mul_assoc] using hclear _ hatx⟩

/-- Only finite generation of the actual colon is needed to clear quotient regularity. -/
theorem exists_notMem_mul_mem_of_isSMulRegular_quotient_atPrime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (I : Ideal R) (a : R)
    (hfinite : (Submodule.comap (LinearMap.mulLeft R a) I).FG)
    (ha : IsSMulRegular
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p)))
      (algebraMap R (Localization.AtPrime p) a)) :
    ∃ g ∉ p, ∀ x : R, a * x ∈ I → g * x ∈ I := by
  let J : Ideal R := Submodule.comap (LinearMap.mulLeft R a) I
  have hJI : J.map (algebraMap R (Localization.AtPrime p)) ≤
      I.map (algebraMap R (Localization.AtPrime p)) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    have hax : a * x ∈ I := hx
    have hmem := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) hax
    rw [map_mul] at hmem
    exact mem_of_isSMulRegular_quotient_of_smul_mem ha hmem
  obtain ⟨g, hg, hmul⟩ :=
    Ideal.exists_mul_mem_of_map_le_atPrime p J I hfinite hJI
  exact ⟨g, hg, fun x hx => hmul x hx⟩

end IsLocalization

namespace RingTheory.Sequence

private theorem ofList_map_mul_unit {R : Type u} [CommRing R]
    (a : R) (ha : IsUnit a) (rs : List R) :
    Ideal.ofList (rs.map (a * ·)) = Ideal.ofList rs := by
  induction rs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, Ideal.ofList_cons, ih, Ideal.span_singleton_mul_left_unit ha]

private theorem isSMulRegular_quotient_congr {R : Type u} [CommRing R]
    {I J : Ideal R} (h : I = J) (a : R) :
    IsSMulRegular (R ⧸ I) a ↔ IsSMulRegular (R ⧸ J) a :=
  (Ideal.quotientEquivAlgOfEq R h).toLinearEquiv.isSMulRegular_congr a

private theorem weaklyRegular_map_mul_unit {R : Type u} [CommRing R]
    (a : R) (ha : IsUnit a) (rs : List R) (h : IsWeaklyRegular R rs) :
    IsWeaklyRegular R (rs.map (a * ·)) := by
  refine ⟨fun i hi => ?_⟩
  have hi' : i < rs.length := by simpa only [List.length_map] using hi
  have hreg := (IsSMulRegular.mul_iff).mpr
    ⟨ha.isSMulRegular _, h.regular_mod_prev i hi'⟩
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at hreg ⊢
  have htake : (rs.map (a * ·)).take i = (rs.take i).map (a * ·) :=
    (List.map_take (f := (a * ·)) (l := rs) (i := i)).symm
  have heq : Ideal.ofList ((rs.map (a * ·)).take i) = Ideal.ofList (rs.take i) :=
    (congrArg Ideal.ofList htake).trans (ofList_map_mul_unit a ha (rs.take i))
  have hnew := (isSMulRegular_quotient_congr heq (a * rs[i])).mpr hreg
  simpa only [List.getElem_map] using hnew

/-- Common-denominator lifting preserves length, regularity and the exact localized ideal. -/
theorem exists_integer_weaklyRegular_list
    {R : Type u} [CommRing R] (M : Submonoid R) (S : Type v) [CommRing S]
    [Algebra R S] [IsLocalization M S] (rs : List S) (hreg : IsWeaklyRegular S rs) :
    ∃ ts : List R, ts.length = rs.length ∧
      IsWeaklyRegular S (ts.map (algebraMap R S)) ∧
      (Ideal.ofList ts).map (algebraMap R S) = Ideal.ofList rs := by
  classical
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite M
    (fun i : Fin rs.length => rs[i])
  choose t ht using hs
  let ts := List.ofFn t
  have hts : ts.map (algebraMap R S) = rs.map (algebraMap R S s * ·) := by
    calc
      ts.map (algebraMap R S) = List.ofFn (fun i => algebraMap R S (t i)) := by
        simp only [ts, List.map_ofFn, Function.comp_def]
      _ = List.ofFn (fun i : Fin rs.length => algebraMap R S s * rs[i]) := by
        apply congrArg List.ofFn
        funext i
        simpa only [Algebra.smul_def] using ht i
      _ = rs.map (algebraMap R S s * ·) := List.ofFn_getElem_eq_map _ _
  have hsunit : IsUnit (algebraMap R S s) := IsLocalization.map_units S s
  refine ⟨ts, by simp only [ts, List.length_ofFn], ?_, ?_⟩
  · rw [hts]
    exact weaklyRegular_map_mul_unit _ hsunit _ hreg
  · rw [Ideal.map_ofList, hts, ofList_map_mul_unit _ hsunit]

/-- Finite prefix colons have one common clearing bound outside the original prime. -/
theorem exists_notMem_mul_mem_prefix_of_atPrime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (rs : List R)
    (hfinite : ∀ i : Fin rs.length,
      (Submodule.comap (LinearMap.mulLeft R rs[i]) (Ideal.ofList (rs.take i))).FG)
    (h : IsWeaklyRegular (Localization.AtPrime p)
      (rs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ g ∉ p, ∀ i : Fin rs.length, ∀ x : R,
      rs[i] * x ∈ Ideal.ofList (rs.take i) → g * x ∈ Ideal.ofList (rs.take i) := by
  classical
  have hi (i : Fin rs.length) : IsSMulRegular
      (Localization.AtPrime p ⧸ (Ideal.ofList (rs.take i)).map
        (algebraMap R (Localization.AtPrime p)))
      (algebraMap R (Localization.AtPrime p) rs[i]) := by
    have hlen : (i : ℕ) < (rs.map (algebraMap R (Localization.AtPrime p))).length := by
      rw [List.length_map]
      exact i.isLt
    have hreg := h.regular_mod_prev i hlen
    rw [Ideal.smul_eq_mul, Ideal.mul_top] at hreg
    have htake := (List.map_take (f := algebraMap R (Localization.AtPrime p))
      (l := rs) (i := (i : ℕ))).symm
    have heq := (congrArg Ideal.ofList htake).trans
      (Ideal.map_ofList (algebraMap R (Localization.AtPrime p)) (rs.take (i : ℕ))).symm
    have hnew := (isSMulRegular_quotient_congr heq
      (rs.map (algebraMap R (Localization.AtPrime p)))[(i : ℕ)]).mp hreg
    simpa only [List.getElem_map, Fin.getElem_fin] using hnew
  have hex (i : Fin rs.length) :=
    IsLocalization.exists_notMem_mul_mem_of_isSMulRegular_quotient_atPrime p
      (Ideal.ofList (rs.take i)) rs[i] (hfinite i) (hi i)
  choose a ha hclear using hex
  let b : p.primeCompl := ∏ i : Fin rs.length, (⟨a i, ha i⟩ : p.primeCompl)
  refine ⟨b, b.property, fun i x hx => ?_⟩
  have hd : (⟨a i, ha i⟩ : p.primeCompl) ∣ b :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨c, hc⟩ := hd
  rw [show (b : R) = a i * c from congrArg Subtype.val hc]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (Ideal.ofList (rs.take i)).mul_mem_left (c : R) (hclear i x hx)

/-- The same prefix bounds give regularity in any original localization inverting the bound. -/
theorem isWeaklyRegular_of_mul_mem_prefix
    {R : Type u} [CommRing R] (M : Submonoid R) (S : Type v) [CommRing S]
    [Algebra R S] [IsLocalization M S] (rs : List R) (g : M)
    (hclear : ∀ i : Fin rs.length, ∀ x : R,
      rs[i] * x ∈ Ideal.ofList (rs.take i) → (g : R) * x ∈ Ideal.ofList (rs.take i)) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) := by
  refine ⟨fun i hi => ?_⟩
  have hi' : i < rs.length := by simpa only [List.length_map] using hi
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have htake := (List.map_take (f := algebraMap R S) (l := rs) (i := i)).symm
  have heq := (congrArg Ideal.ofList htake).trans
    (Ideal.map_ofList (algebraMap R S) (rs.take i)).symm
  have hcur : IsSMulRegular (S ⧸ (Ideal.ofList (rs.take i)).map (algebraMap R S))
      (algebraMap R S rs[i]) := by
    exact IsLocalization.isSMulRegular_quotient_of_mul_mem M S
      (Ideal.ofList (rs.take i)) rs[i] g (fun x hx => hclear ⟨i, hi'⟩ x hx)
  have hnew := (isSMulRegular_quotient_congr heq (algebraMap R S rs[i])).mpr hcur
  simpa only [List.getElem_map] using hnew

/-- The original neighbouring-prime interface is a specialization of the common prefix bound. -/
theorem exists_weaklyRegular_atPrime_of_weaklyRegular_atPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (rs : List R)
    (h : IsWeaklyRegular (Localization.AtPrime p)
      (rs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ a ∉ p, ∀ (q : Ideal R) [q.IsPrime], a ∉ q →
      IsWeaklyRegular (Localization.AtPrime q)
        (rs.map (algebraMap R (Localization.AtPrime q))) := by
  obtain ⟨a, ha, hclear⟩ := exists_notMem_mul_mem_prefix_of_atPrime p rs
    (fun i => Ideal.fg_of_isNoetherianRing
      (Submodule.comap (LinearMap.mulLeft R rs[i]) (Ideal.ofList (rs.take i)))) h
  refine ⟨a, ha, fun q _ haq => ?_⟩
  exact isWeaklyRegular_of_mul_mem_prefix q.primeCompl (Localization.AtPrime q)
    rs ⟨a, haq⟩ hclear

end RingTheory.Sequence
