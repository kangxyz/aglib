/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.MixedGeneration
public import Aglib.KTheory.MilnorK.Residue.BaseChangeSupport

/-!
# Finite split-polynomial witnesses for mixed generation

An actual symbol of nonzero split polynomials lies in the second polynomial
stage by coordinatewise multiplicativity. Specialization therefore gives a
mixed class when the indicated representative polynomials split. The inputs
are the finite coordinates of the actual symbol, not a global degree-gap
assumption on the coefficient field.
-/

@[expose] public noncomputable section

namespace MilnorK.DegreeFiltration

open Polynomial PolynomialResidue Polynomial.LocalResidue

variable {k L : Type*} [Field k] [Field L]

/-- Split polynomial units are generated multiplicatively by units of constant
and linear polynomials. Only nonzero factors enter the rational-function field. -/
theorem polynomialUnit_property_of_splits (P : (RatFunc k)ˣ → Prop)
    (hone : P 1) (hmul : ∀ u v, P u → P v → P (u * v))
    (hsmall : ∀ (q : k[X]) (hq : q ≠ 0), q.natDegree < 2 → P (polynomialUnit k q hq))
    (q : k[X]) (hq : q ≠ 0) (hsplit : q.Splits) : P (polynomialUnit k q hq) := by
  revert hq
  induction hsplit using Submonoid.closure_induction with
  | mem q hq =>
    intro hne
    rcases hq with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact hsmall _ hne (by simp)
    · exact hsmall _ hne (by simp)
  | one =>
    intro _
    simpa only [polynomialUnit_one] using hone
  | mul q r _ _ ihq ihr =>
    intro hqr
    have hq := left_ne_zero_of_mul hqr
    have hr := right_ne_zero_of_mul hqr
    rw [polynomialUnit_mul q r hq hr]
    exact hmul _ _ (ihq hq) (ihr hr)

/-- A rational symbol whose finite polynomial coordinates all split lies in
the actual second stage, in every Milnor degree. -/
theorem polynomial_symbol_mem_lower_two_of_splits (n : ℕ) (a : Fin n → k[X])
    (ha : ∀ i, a i ≠ 0) (hsplit : ∀ i, (a i).Splits) :
    symbol (polynomialTuple a ha) ∈ lower k n 2 := by
  let s : Set (RatFunc k)ˣ := {u | ∃ (q : k[X]) (hq : q ≠ 0),
    q.natDegree < 2 ∧ u = polynomialUnit k q hq}
  apply symbol_mem_of_coordinate_span (lower k n 2) s
  · intro b hb
    choose q hq hqd hqb using hb
    have heq : b = polynomialTuple q hq := funext hqb
    rw [heq]
    exact polynomial_symbol_mem_lower 2 q hq hqd
  · intro i
    apply polynomialUnit_property_of_splits
      (fun u => Additive.ofMul u ∈ Submodule.span ℤ (Additive.ofMul '' s))
      (Submodule.zero_mem _) (fun _ _ hu hv => Submodule.add_mem _ hu hv)
      (fun q hq hqd => Submodule.subset_span ⟨_, ⟨q, hq, hqd, rfl⟩, rfl⟩)
      (a i) (ha i) (hsplit i)

/-- Specialization of a split polynomial tuple is in the actual mixed span
when the specified modulus has degree greater than one. -/
theorem specialize_split_polynomial_mem_mixed (p : k[X]) [Fact (Irreducible p)]
    (hp : 1 < p.natDegree) (m : ℕ) (a : Fin (m + 1) → k[X])
    (ha : ∀ i, a i ≠ 0) (hsplit : ∀ i, (a i).Splits) :
    specializeAt p (m + 1) (symbol (polynomialTuple a ha)) ∈
      mixedSpan (algebraMap k (AdjoinRoot p)) m :=
  lower_two_le_comap_specialize_mixed p hp m
    (polynomial_symbol_mem_lower_two_of_splits (m + 1) a ha hsplit)

/-- After the literal coefficient map, only the supplied coordinate
polynomials need to split for the actual rational symbol to lie in stage two. -/
theorem map_polynomial_symbol_mem_lower_two_of_splits (φ : k →+* L)
    (n : ℕ) (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (hsplit : ∀ i, ((a i).map φ).Splits) :
    MilnorK.map n (fractionMap φ) (symbol (polynomialTuple a ha)) ∈ lower L n 2 := by
  rw [MilnorK.map_symbol]
  have heq : Units.map (fractionMap φ).toMonoidHom ∘ polynomialTuple a ha =
      polynomialTuple (fun i => (a i).map φ) (fun i => Polynomial.map_ne_zero (ha i)) := by
    funext i
    exact unitsMap_polynomialUnit φ (a i) (ha i)
  rw [heq]
  exact polynomial_symbol_mem_lower_two_of_splits n _ _ hsplit

end MilnorK.DegreeFiltration

namespace MilnorK

open Polynomial PolynomialResidue Polynomial.LocalResidue DegreeFiltration

variable {k L : Type*} [Field k] [Field L]

/-- At an actual irreducible factor after coefficient extension, a source
symbol becomes mixed if its finitely many canonical representatives split.
Both root fields and the factor divisibility are explicit; no global degree
gap or prime-degree irreducibility transport is assumed. -/
theorem restricted_symbol_mem_mixed_of_reduced_splits (φ : k →+* L)
    (p : MonicIrreducible k) (q : MonicIrreducible L) (hq : q.val ∣ p.val.map φ)
    (m : ℕ) (a : SymbolTuple (AdjoinRoot p.val) (m + 1))
    (hsplit : ∀ i, ((reducedRepresentative p.val p.property.1 (a i)).map φ).Splits) :
    map (m + 1) (adjoinRootMap φ p.val q.val hq) (symbol a) ∈
      mixedSpan (algebraMap L (AdjoinRoot q.val)) m := by
  by_cases hq1 : q.val.natDegree = 1
  · rw [mixedSpan_eq_top_of_natDegree_le_two q (by omega) m]
    trivial
  · let r : Fin (m + 1) → L[X] := fun i =>
      (reducedRepresentative p.val p.property.1 (a i)).map φ
    have hr : ∀ i, r i ≠ 0 := fun i =>
      Polynomial.map_ne_zero (reducedRepresentative_ne_zero p.val p.property.1 (a i))
    have heval (i : Fin (m + 1)) : AdjoinRoot.mk q.val (r i) =
        adjoinRootMap φ p.val q.val hq (a i : AdjoinRoot p.val) := by
      change AdjoinRoot.mk q.val
        ((reducedRepresentative p.val p.property.1 (a i)).map φ) = _
      rw [← adjoinRootMap_mk φ p.val q.val hq, mk_reducedRepresentative]
    have hqr : ∀ i, ¬ q.val ∣ r i := by
      intro i hdiv
      have hz := AdjoinRoot.mk_eq_zero.mpr hdiv
      rw [heval] at hz
      exact (Units.map (adjoinRootMap φ p.val q.val hq).toMonoidHom (a i)).ne_zero hz
    have hspec : specializeAt q.val (m + 1) (symbol (polynomialTuple r hr)) =
        map (m + 1) (adjoinRootMap φ p.val q.val hq) (symbol a) := by
      change specializeAt q.val (m + 1)
        (symbol (fun i => PolynomialResidue.polynomialUnit (r i) (hr i))) = _
      rw [specializeAt_polynomial_units q.val (m + 1) r hr hqr, map_symbol]
      congr 1
      funext i
      apply Units.ext
      exact heval i
    rw [← hspec]
    exact specialize_split_polynomial_mem_mixed q.val
      (by have := q.property.2.natDegree_pos; omega) m r hr hsplit

/-- Membership in the actual mixed span supplies finite integer coefficients
and the literal base-tuple/extension-unit witnesses. -/
theorem exists_mixed_expansion_of_mem (φ : k →+* L) (m : ℕ) (x : K L (m + 1))
    (hx : x ∈ mixedSpan φ m) :
    ∃ c : (SymbolTuple k m × Lˣ) →₀ ℤ,
      (c.sum fun ab z => z • symbol (Fin.snoc (Units.map φ.toMonoidHom ∘ ab.1) ab.2)) = x := by
  apply Finsupp.mem_span_range_iff_exists_finsupp.mp
  have hs : {z | ∃ (a : SymbolTuple k m) (b : Lˣ),
      z = symbol (Fin.snoc (Units.map φ.toMonoidHom ∘ a) b)} =
      Set.range (fun ab : SymbolTuple k m × Lˣ =>
        symbol (Fin.snoc (Units.map φ.toMonoidHom ∘ ab.1) ab.2)) := by
    ext z
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨(a, b), rfl⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, b, rfl⟩
  rw [← hs]
  exact hx

universe u v

/-- Every original class has a finite collection of nonzero reduced polynomial
witnesses. Over any coefficient field where these particular polynomials split,
its image at every actual irreducible factor lies in the mixed span. The
witnesses are chosen before the coefficient field and factor. -/
theorem exists_finite_reduced_splitting_witness {k : Type u} [Field k]
    (p : MonicIrreducible k) (m : ℕ) (x : K (AdjoinRoot p.val) (m + 1)) :
    ∃ s : Finset k[X],
      (∀ r ∈ s, r ≠ 0 ∧ r.natDegree < p.val.natDegree) ∧
      ∀ (L : Type v) [Field L] (φ : k →+* L) (q : MonicIrreducible L)
        (hq : q.val ∣ p.val.map φ),
        (∀ r ∈ s, (r.map φ).Splits) →
        map (m + 1) (adjoinRootMap φ p.val q.val hq) x ∈
          mixedSpan (algebraMap L (AdjoinRoot q.val)) m := by
  classical
  obtain ⟨z, rfl⟩ := (relationSpan (AdjoinRoot p.val) (m + 1)).mkQ_surjective x
  let s : Finset k[X] := z.support.biUnion fun a =>
    Finset.univ.image fun i => reducedRepresentative p.val p.property.1 (a i)
  have hmem (a : SymbolTuple (AdjoinRoot p.val) (m + 1)) (ha : a ∈ z.support)
      (i : Fin (m + 1)) : reducedRepresentative p.val p.property.1 (a i) ∈ s :=
    Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  refine ⟨s, ?_, ?_⟩
  · intro r hr
    obtain ⟨a, _, hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨reducedRepresentative_ne_zero p.val p.property.1 (a i),
      reducedRepresentative_natDegree_lt p.val p.property.1 (a i)⟩
  · intro L _ φ q hq hsplit
    have hz : (relationSpan (AdjoinRoot p.val) (m + 1)).mkQ z =
        z.sum (fun a c => c • symbol a) := by
      have h : (relationSpan (AdjoinRoot p.val) (m + 1)).mkQ =
          Finsupp.linearCombination ℤ (fun a => symbol a) := by
        apply Finsupp.lhom_ext
        intro a c
        rw [Finsupp.linearCombination_single]
        change (relationSpan (AdjoinRoot p.val) (m + 1)).mkQ (Finsupp.single a c) =
          c • (relationSpan (AdjoinRoot p.val) (m + 1)).mkQ (Finsupp.single a 1)
        rw [← LinearMap.map_smul]
        congr 1
        simp
      exact LinearMap.congr_fun h z
    rw [hz]
    simp only [Finsupp.sum, map_sum, LinearMap.map_smul]
    apply Submodule.sum_mem
    intro a ha
    apply Submodule.smul_mem
    exact restricted_symbol_mem_mixed_of_reduced_splits φ p q hq m a
      (fun i => hsplit _ (hmem a ha i))

/-- Finite splitting witnesses give an actual finite signed mixed expansion
of the restricted class, for every future coefficient field and actual factor. -/
theorem exists_finite_reduced_mixed_expansion {k : Type u} [Field k]
    (p : MonicIrreducible k) (m : ℕ) (x : K (AdjoinRoot p.val) (m + 1)) :
    ∃ s : Finset k[X],
      (∀ r ∈ s, r ≠ 0 ∧ r.natDegree < p.val.natDegree) ∧
      ∀ (L : Type v) [Field L] (φ : k →+* L) (q : MonicIrreducible L)
        (hq : q.val ∣ p.val.map φ),
        (∀ r ∈ s, (r.map φ).Splits) →
        ∃ c : (SymbolTuple L m × (AdjoinRoot q.val)ˣ) →₀ ℤ,
          (c.sum fun ab z => z • symbol (Fin.snoc
            (Units.map (algebraMap L (AdjoinRoot q.val)).toMonoidHom ∘ ab.1) ab.2)) =
              map (m + 1) (adjoinRootMap φ p.val q.val hq) x := by
  obtain ⟨s, hs, hgen⟩ := exists_finite_reduced_splitting_witness.{u, v} p m x
  refine ⟨s, hs, ?_⟩
  intro L _ φ q hq hsplit
  exact exists_mixed_expansion_of_mem (algebraMap L (AdjoinRoot q.val)) m _
    (hgen L φ q hq hsplit)

end MilnorK
