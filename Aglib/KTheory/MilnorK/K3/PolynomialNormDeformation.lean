/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PrincipalUnitResidue

/-!
# Actual polynomial norms under a finite monic deformation

The actual total residue of `{p/q,A,B}` compares the sums of actual polynomial
norms at the irreducible factors of equal-degree monic polynomials `p` and `q`.
The normalized-factor multiset retains every repeated factor. All residue-field
entries are literal quotient units. Principal-unit vanishing handles the finite
places dividing `A * B` and the infinity place, without a pole restriction on
`A` or `B`.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.PolynomialNorm

open Polynomial PolynomialResidue MilnorK.K2
open UniqueFactorizationMonoid

variable {k : Type*} [Field k]

/-- The literal monic irreducible factors, with their full multiplicities. -/
def factorPlaces (f : k[X]) (hf : f ≠ 0) : Multiset (MonicIrreducible k) := by
  classical
  exact (normalizedFactors f).attach.map fun r =>
    ⟨r.val, ((Polynomial.mem_normalizedFactors_iff hf).mp r.property).2.1,
      ((Polynomial.mem_normalizedFactors_iff hf).mp r.property).1⟩

open scoped Classical in
/-- Forgetting the place structure recovers the normalized-factor multiset. -/
theorem factorPlaces_map_val (f : k[X]) (hf : f ≠ 0) :
    (factorPlaces f hf).map Subtype.val = normalizedFactors f := by
  classical
  simp only [factorPlaces, Multiset.map_map, Function.comp_def, Multiset.attach_map_val]

/-- Membership of the place multiset means literal polynomial divisibility. -/
theorem mem_factorPlaces_iff (f : k[X]) (hf : f ≠ 0) (r : MonicIrreducible k) :
    r ∈ factorPlaces f hf ↔ r.val ∣ f := by
  classical
  have hmem : r ∈ factorPlaces f hf ↔ r.val ∈ (factorPlaces f hf).map Subtype.val :=
    (Multiset.mem_map_of_injective Subtype.val_injective).symm
  rw [hmem, factorPlaces_map_val, Polynomial.mem_normalizedFactors_iff hf]
  exact ⟨fun h => h.2.2, fun h => ⟨r.property.2, r.property.1, h⟩⟩

/-- A factor of a polynomial coprime to `A * B` is prime to both entries. -/
theorem factorPlaces_not_dvd (f A B : k[X]) (hf : f ≠ 0)
    (hcop : IsCoprime f (A * B)) (r : MonicIrreducible k)
    (hr : r ∈ factorPlaces f hf) : ¬ r.val ∣ A ∧ ¬ r.val ∣ B := by
  have hrf := (mem_factorPlaces_iff f hf r).mp hr
  exact ⟨fun h => r.property.2.not_isUnit
    (hcop.isUnit_of_dvd' hrf (dvd_mul_of_dvd_left h B)),
    fun h => r.property.2.not_isUnit
      (hcop.isUnit_of_dvd' hrf (dvd_mul_of_dvd_right h A))⟩

/-- The original quotient-field symbol at an actual factor. -/
def factorSymbol (f A B : k[X]) (hf : f ≠ 0) (hcop : IsCoprime f (A * B))
    (r : {r : MonicIrreducible k // r ∈ factorPlaces f hf}) :
    MilnorK.K2.Group (AdjoinRoot r.val.val) :=
  symbol (quotientUnit r.val.val A (factorPlaces_not_dvd f A B hf hcop r.val r.property).1)
    (quotientUnit r.val.val B (factorPlaces_not_dvd f A B hf hcop r.val r.property).2)

/-- The original dependent finite residue vector, summed with factor multiplicity. -/
def factorResidues (f A B : k[X]) (hf : f.Monic) (hcop : IsCoprime f (A * B)) :
    Π₀ r : MonicIrreducible k, MilnorK.K2.Group (AdjoinRoot r.val) := by
  classical
  exact ((factorPlaces f hf.ne_zero).attach.map fun r =>
    DFinsupp.single r.val (factorSymbol f A B hf.ne_zero hcop r)).sum

/-- The sum of actual polynomial norms of the literal factor symbols. -/
def factorNormSum (f A B : k[X]) (hf : f.Monic) (hcop : IsCoprime f (A * B)) :
    MilnorK.K2.Group k := by
  classical
  exact ((factorPlaces f hf.ne_zero).attach.map fun
    (r : {r : MonicIrreducible k // r ∈ factorPlaces f hf.ne_zero}) =>
    polynomialNorm (k := k) r.val (factorSymbol f A B hf.ne_zero hcop r)).sum

/-- Applying the constructed total norm gives precisely the literal factor sum. -/
theorem totalNorm_factorResidues (f A B : k[X]) (hf : f.Monic)
    (hcop : IsCoprime f (A * B)) :
    totalNorm (factorResidues f A B hf hcop) = factorNormSum f A B hf hcop := by
  classical
  simp only [factorResidues, factorNormSum, map_multiset_sum, Multiset.map_map,
    Function.comp_def, totalNorm_single]

private theorem polynomialUnit_factorPlaces (f : k[X]) (hf : f.Monic) :
    ((factorPlaces f hf.ne_zero).map fun r => polynomialUnit r.val r.property.2.ne_zero).prod =
      polynomialUnit f hf.ne_zero := by
  classical
  apply Units.ext
  change (Units.coeHom (RatFunc k)) _ = algebraMap k[X] (RatFunc k) f
  rw [map_multiset_prod, Multiset.map_map]
  change ((factorPlaces f hf.ne_zero).map fun r =>
    algebraMap k[X] (RatFunc k) r.val).prod = _
  change ((factorPlaces f hf.ne_zero).map
    ((algebraMap k[X] (RatFunc k)) ∘ Subtype.val)).prod = _
  rw [← Multiset.map_map, ← map_multiset_prod, factorPlaces_map_val]
  have hfactor := Polynomial.leadingCoeff_mul_prod_normalizedFactors f
  rw [hf.leadingCoeff, C_1, one_mul] at hfactor
  rw [hfactor]

private theorem symbol3_multiset_prod (s : Multiset (RatFunc k)ˣ)
    (a b : (RatFunc k)ˣ) :
    symbol3 s.prod a b = (s.map fun u => symbol3 u a b).sum := by
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.prod_zero, symbol3_one_left, Multiset.map_zero, Multiset.sum_zero]
  | cons u s ih =>
    simp only [Multiset.prod_cons, symbol3_mul_left, ih, Multiset.map_cons, Multiset.sum_cons]

/-- Factorization of the first polynomial entry inside the actual original `K3`. -/
theorem symbol3_factorPlaces (f : k[X]) (hf : f.Monic) (a b : (RatFunc k)ˣ) :
    symbol3 (polynomialUnit f hf.ne_zero) a b =
      ((factorPlaces f hf.ne_zero).map fun r =>
        symbol3 (polynomialUnit r.val r.property.2.ne_zero) a b).sum := by
  rw [← polynomialUnit_factorPlaces f hf, symbol3_multiset_prod, Multiset.map_map]
  rfl

/-- Away from the two other entries, first-slot factorization gives precisely
our literal factor-residue vector. -/
theorem residueAt_eq_factorResidues (f A B : k[X]) (hf : f.Monic)
    (hA : A ≠ 0) (hB : B ≠ 0) (hcop : IsCoprime f (A * B))
    (r : MonicIrreducible k) (hrA : ¬ r.val ∣ A) (hrB : ¬ r.val ∣ B) :
    residueAt r.val (symbol3 (polynomialUnit f hf.ne_zero)
      (polynomialUnit A hA) (polynomialUnit B hB)) =
      factorResidues f A B hf hcop r := by
  classical
  rw [symbol3_factorPlaces f hf, map_multiset_sum, Multiset.map_map]
  change _ = DFinsupp.evalAddMonoidHom r (factorResidues f A B hf hcop)
  rw [factorResidues, map_multiset_sum, Multiset.map_map]
  simp only [Function.comp_def]
  rw [← Multiset.attach_map_val' (factorPlaces f hf.ne_zero)
    (fun q => residueAt r.val (symbol3 (polynomialUnit q.val q.property.2.ne_zero)
      (polynomialUnit A hA) (polynomialUnit B hB)))]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro q _
  change residueAt r.val (symbol3 (polynomialUnit q.val.val q.val.property.2.ne_zero)
    (polynomialUnit A hA) (polynomialUnit B hB)) =
    (DFinsupp.single (β := fun r : MonicIrreducible k => MilnorK.K2.Group (AdjoinRoot r.val))
    q.val (factorSymbol f A B hf.ne_zero hcop q)) r
  by_cases hqr : q.val = r
  · subst r
    rw [DFinsupp.single_eq_same, residueAt_polynomial_units _ _ _ _ _ hrA hrB]
    rfl
  · rw [DFinsupp.single_eq_of_ne (Ne.symm hqr)]
    exact residueAt_polynomial_units_zero r.val q.val.val A B
      q.val.property.2.ne_zero hA hB (not_dvd_of_ne q.val r hqr) hrA hrB

/-- A place outside the literal factors has zero component in the factor vector. -/
theorem factorResidues_apply_eq_zero (f A B : k[X]) (hf : f.Monic)
    (hcop : IsCoprime f (A * B)) (r : MonicIrreducible k) (hr : ¬ r.val ∣ f) :
    factorResidues f A B hf hcop r = 0 := by
  classical
  change DFinsupp.evalAddMonoidHom r (factorResidues f A B hf hcop) = 0
  rw [factorResidues, map_multiset_sum, Multiset.map_map]
  apply Multiset.sum_eq_zero
  intro x hx
  obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hx
  change (DFinsupp.single (β := fun r : MonicIrreducible k => MilnorK.K2.Group (AdjoinRoot r.val))
    q.val (factorSymbol f A B hf.ne_zero hcop q)) r = 0
  apply DFinsupp.single_eq_of_ne
  intro h
  apply hr
  rw [h]
  exact (mem_factorPlaces_iff f hf.ne_zero q.val).mp q.property

/-- Divisibility of a polynomial difference is equality of literal quotient units. -/
theorem quotientUnit_eq_of_dvd_sub (r : MonicIrreducible k) (p q : k[X])
    (hrp : ¬ r.val ∣ p) (hrq : ¬ r.val ∣ q) (hpq : r.val ∣ p - q) :
    quotientUnit r.val p hrp = quotientUnit r.val q hrq := by
  apply Units.ext
  change AdjoinRoot.mk r.val p = AdjoinRoot.mk r.val q
  apply sub_eq_zero.mp
  rw [← map_sub, AdjoinRoot.mk_eq_zero]
  exact hpq

/-- The full actual finite residue vector of the monic deformation is the
factor-residue difference, including every repeated factor. -/
theorem totalResidue_monic_deformation (p q A B : k[X]) (hp : p.Monic) (hq : q.Monic)
    (hA : A ≠ 0) (hB : B ≠ 0) (hpc : IsCoprime p (A * B))
    (hqc : IsCoprime q (A * B)) (hmod : A * B ∣ p - q) :
    totalResidue (symbol3 (polynomialUnit p hp.ne_zero / polynomialUnit q hq.ne_zero)
      (polynomialUnit A hA) (polynomialUnit B hB)) =
      factorResidues p A B hp hpc - factorResidues q A B hq hqc := by
  classical
  apply DFinsupp.ext
  intro r
  rw [totalResidue_apply, DFinsupp.sub_apply]
  by_cases hr : r.val ∣ A * B
  · have hrp : ¬ r.val ∣ p := fun h => r.property.2.not_isUnit (hpc.isUnit_of_dvd' h hr)
    have hrq : ¬ r.val ∣ q := fun h => r.property.2.not_isUnit (hqc.isUnit_of_dvd' h hr)
    rw [factorResidues_apply_eq_zero p A B hp hpc r hrp,
      factorResidues_apply_eq_zero q A B hq hqc r hrq, sub_zero]
    exact residueAt_polynomial_ratio_eq_zero r.val p q hp.ne_zero hq.ne_zero hrp hrq
      (quotientUnit_eq_of_dvd_sub r p q hrp hrq (dvd_trans hr hmod)) _ _
  · have hrA : ¬ r.val ∣ A := fun h => hr (dvd_mul_of_dvd_left h B)
    have hrB : ¬ r.val ∣ B := fun h => hr (dvd_mul_of_dvd_right h A)
    rw [symbol3_div_left, map_sub,
      residueAt_eq_factorResidues p A B hp hA hB hpc r hrA hrB,
      residueAt_eq_factorResidues q A B hq hA hB hqc r hrA hrB]

/-- Actual polynomial norm recurrence for equal-degree monic deformations.
Both finite bad places and infinity are handled by proved principal-unit
vanishing; no compatibility or reciprocity hypothesis is assumed. -/
theorem factorNormSum_eq_of_monic_deformation (p q A B : k[X])
    (hp : p.Monic) (hq : q.Monic) (hdeg : p.natDegree = q.natDegree)
    (hA : A ≠ 0) (hB : B ≠ 0) (hpc : IsCoprime p (A * B))
    (hqc : IsCoprime q (A * B)) (hmod : A * B ∣ p - q) :
    factorNormSum p A B hp hpc = factorNormSum q A B hq hqc := by
  have h := totalNorm_totalResidue
    (symbol3 (polynomialUnit p hp.ne_zero / polynomialUnit q hq.ne_zero)
      (polynomialUnit A hA) (polynomialUnit B hB))
  rw [totalResidue_monic_deformation p q A B hp hq hA hB hpc hqc hmod,
    map_sub, totalNorm_factorResidues, totalNorm_factorResidues,
    InfinityResidue.residue_monic_ratio p q hp hq hdeg, neg_zero] at h
  exact sub_eq_zero.mp h

open scoped Classical in
/-- Place multiplicity is exactly normalized-factor multiplicity. -/
theorem count_factorPlaces (f : k[X]) (hf : f ≠ 0) (r : MonicIrreducible k) :
    (factorPlaces f hf).count r = (normalizedFactors f).count r.val := by
  classical
  have h := Multiset.count_map_eq_count' Subtype.val (factorPlaces f hf)
    Subtype.val_injective r
  rw [factorPlaces_map_val] at h
  exact h.symm

/-- An irreducible polynomial has exactly its one literal factor place. -/
theorem factorPlaces_irreducible (p : MonicIrreducible k) :
    factorPlaces p.val p.property.1.ne_zero = {p} := by
  classical
  apply Multiset.map_injective Subtype.val_injective
  rw [factorPlaces_map_val, normalizedFactors_irreducible p.property.2,
    p.property.1.normalize_eq_self, Multiset.map_singleton]

open scoped Classical in
/-- Reindexing a literal factor sum by divisors records multiplicity as a
coefficient. This applies to any additive target, including actual cycle groups. -/
theorem factorPlaces_sum_eq_sum_count {M : Type*} [AddCommMonoid M]
    (f : k[X]) (hf : f ≠ 0)
    [Fintype {r : MonicIrreducible k // r.val ∣ f}]
    (g : {r : MonicIrreducible k // r.val ∣ f} → M) :
    ((factorPlaces f hf).attach.map (fun r =>
      g ⟨r.val, (mem_factorPlaces_iff f hf r.val).mp r.property⟩)).sum =
      ∑ r : {r : MonicIrreducible k // r.val ∣ f},
        (normalizedFactors f).count r.val.val • g r := by
  classical
  rw [Finset.sum_multiset_map_count]
  apply Finset.sum_bij (fun r _ =>
    (⟨r.val, (mem_factorPlaces_iff f hf r.val).mp r.property⟩ :
      {r : MonicIrreducible k // r.val ∣ f}))
  · intro r _
    exact Finset.mem_univ _
  · intro r _ s _ hrs
    apply Subtype.ext
    exact congrArg (fun x : {r : MonicIrreducible k // r.val ∣ f} => x.val) hrs
  · intro r _
    exact ⟨⟨r.val, (mem_factorPlaces_iff f hf r.val).mpr r.property⟩,
      by simp only [Multiset.mem_toFinset, Multiset.mem_attach], rfl⟩
  · intro r _
    rw [Multiset.count_attach, count_factorPlaces]

/-- For one irreducible factor the sum is the original polynomial norm itself. -/
theorem factorNormSum_irreducible (p : MonicIrreducible k) (A B : k[X])
    (hcop : IsCoprime p.val (A * B)) (hrA : ¬ p.val ∣ A) (hrB : ¬ p.val ∣ B) :
    factorNormSum p.val A B p.property.1 hcop =
      polynomialNorm p (symbol (quotientUnit p.val A hrA) (quotientUnit p.val B hrB)) := by
  classical
  have hsingle : factorResidues p.val A B p.property.1 hcop =
      DFinsupp.single p (symbol (quotientUnit p.val A hrA) (quotientUnit p.val B hrB)) := by
    apply DFinsupp.ext
    intro r
    by_cases hrp : r = p
    · subst r
      have hA : A ≠ 0 := fun h => hrA (h ▸ dvd_zero p.val)
      have hB : B ≠ 0 := fun h => hrB (h ▸ dvd_zero p.val)
      rw [DFinsupp.single_eq_same,
        ← residueAt_eq_factorResidues p.val A B p.property.1 hA hB hcop p hrA hrB,
        residueAt_polynomial_units]
    · rw [DFinsupp.single_eq_of_ne hrp]
      exact factorResidues_apply_eq_zero p.val A B p.property.1 hcop r
        (not_dvd_of_ne p r (Ne.symm hrp))
  rw [← totalNorm_factorResidues, hsingle, totalNorm_single]

end MilnorK.K3.PolynomialNorm
