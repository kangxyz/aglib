/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSections
public import Mathlib.RingTheory.Ideal.Operations
/-!
# Finite principal-cover degree-one Cech exactness

Work with actual sections and actual restrictions of a quasicoherent sheaf.
The numerator and torsion clearing steps retain the given cocycle and require
neither noetherianity nor a nonzero base ring.

The main theorem `exists_cechOne_coboundary` solves the original section-valued
cocycle equation on a finite principal cover. It does not yet identify the
result with the derived sheaf-cohomology object.

Reference: Stacks Project, [Tag 01X9](https://stacks.math.columbia.edu/tag/01X9).
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PrimeSpectrum

namespace AlgebraicGeometry.Scheme.Modules.AffineCech

variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

/-- Actual sections with their natural module structure over the base ring. -/
abbrev Section (U : (Spec R).Opens) := (modulesSpecToSheaf.obj M).obj.obj (op U)

/-- Actual restriction as a base-linear map. -/
abbrev res {U V : (Spec R).Opens} (h : V ≤ U) : Section M U →ₗ[R] Section M V :=
  ((modulesSpecToSheaf.obj M).obj.map (homOfLE h).op).hom

lemma res_res {U V W : (Spec R).Opens} (hUV : V ≤ U) (hVW : W ≤ V)
    (s : Section M U) : res M hVW (res M hUV s) = res M (hVW.trans hUV) s := by
  change (((modulesSpecToSheaf.obj M).obj.map (homOfLE hUV).op) ≫
    ((modulesSpecToSheaf.obj M).obj.map (homOfLE hVW).op)) s = _
  rw [← Functor.map_comp]
  rfl

variable [M.IsQuasicoherent] {ι : Type v} [Finite ι]

/-- Finitely many sections on principal overlaps admit one simultaneous
numerator exponent, but the numerators have not yet been made compatible. -/
lemma exists_uniform_overlap_numerators (f : ι → R)
    (c : ∀ i k, Section M (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f k))) :
    ∃ (N : ℕ) (t : ∀ i _k : ι, Section M (PrimeSpectrum.basicOpen (f i))), ∀ i k,
      res M (inf_le_left : PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f k) ≤ _)
          (t i k) =
        f k ^ N • c i k := by
  classical
  have h (i k : ι) : ∃ (n : ℕ) (t : Section M (PrimeSpectrum.basicOpen (f i))),
      res M inf_le_left t = f k ^ n • c i k :=
    (Scheme.Modules.QuasiCoherent.AffineSections.clearsDenominators_basicOpen
      M (f i) (f k)).existence (c i k)
  choose n t ht using h
  let N := ⨆ i, ⨆ k, n i k
  refine ⟨N, fun i k => f k ^ (N - n i k) • t i k, fun i k => ?_⟩
  have hn : n i k ≤ N :=
    le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) k)
  have hN : N = (N - n i k) + n i k := by omega
  rw [LinearMap.map_smul, ht, ← mul_smul, ← pow_add, ← hN]

omit [Finite ι] in
/-- Denominator torsion on a pairwise principal intersection is genuinely
killed by a power of the third principal-open coordinate. -/
lemma exists_overlap_torsion_power (f : ι → R) (i j k : ι)
    (s : Section M (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)))
    (hs : res M (inf_le_left : (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)) ⊓
      PrimeSpectrum.basicOpen (f k) ≤ _) s = 0) : ∃ n : ℕ, f k ^ n • s = 0 := by
  have h : Scheme.Modules.QuasiCoherent.AffineSections.ClearsDenominators M
      (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)) (f k) := by
    rw [← PrimeSpectrum.basicOpen_mul]
    exact Scheme.Modules.QuasiCoherent.AffineSections.clearsDenominators_basicOpen
      M (f i * f j) (f k)
  exact h.uniqueness s hs

/-- A finite section-valued Cech 1-cocycle has compatible numerators after
one uniform power. The second denominator step kills actual overlap torsion. -/
lemma exists_uniform_cocycle_numerators (f : ι → R)
    (c : ∀ i j, Section M (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)))
    (hc : ∀ i j k,
      res M (inf_le_left : (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)) ⊓
          PrimeSpectrum.basicOpen (f k) ≤ _)
          (c i j) +
        res M (inf_le_inf inf_le_right le_rfl) (c j k) =
        res M (inf_le_inf inf_le_left le_rfl) (c i k)) :
    ∃ (N : ℕ) (t : ∀ i _k : ι, Section M (PrimeSpectrum.basicOpen (f i))), ∀ i j k,
      res M (inf_le_left : PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j) ≤ _)
          (t i k) -
        res M inf_le_right (t j k) = f k ^ N • c i j := by
  classical
  obtain ⟨N, t, ht⟩ := exists_uniform_overlap_numerators M f c
  let d (i j k : ι) : Section M (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)) :=
    res M inf_le_left (t i k) - res M inf_le_right (t j k) - f k ^ N • c i j
  have hd (i j k : ι) : ∃ n : ℕ, f k ^ n • d i j k = 0 := by
    apply exists_overlap_torsion_power M f i j k
    have hi := congrArg (res M
      (V := (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)) ⊓
        PrimeSpectrum.basicOpen (f k))
      (inf_le_inf inf_le_left le_rfl)) (ht i k)
    have hj := congrArg (res M
      (V := (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)) ⊓
        PrimeSpectrum.basicOpen (f k))
      (inf_le_inf inf_le_right le_rfl)) (ht j k)
    simp only [res_res, LinearMap.map_smul] at hi hj
    dsimp [d]
    simp only [map_sub, LinearMap.map_smul, res_res]
    rw [hi, hj, ← hc i j k, smul_add]
    abel
  choose n hn using hd
  let K := ⨆ i, ⨆ j, ⨆ k, n i j k
  refine ⟨K + N, fun i k => f k ^ K • t i k, fun i j k => ?_⟩
  have hnK : n i j k ≤ K := le_ciSup_of_le (Finite.bddAbove_range _) i
    (le_ciSup_of_le (Finite.bddAbove_range _) j (le_ciSup (Finite.bddAbove_range _) k))
  have hK : K = (K - n i j k) + n i j k := by omega
  have hdK : f k ^ K • d i j k = 0 := by
    rw [hK, pow_add, mul_smul, hn, smul_zero]
  simpa only [d, smul_sub, ← mul_smul, ← pow_add, sub_eq_zero, LinearMap.map_smul] using hdK

/-- Every actual section-valued Cech 1-cocycle for a finite principal cover
of an affine scheme is a coboundary. The result holds for arbitrary
quasicoherent sheaves over arbitrary commutative rings. -/
theorem exists_cechOne_coboundary (f : ι → R)
    (hcover : (⨆ i, PrimeSpectrum.basicOpen (f i)) = ⊤)
    (c : ∀ i j, Section M (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)))
    (hc : ∀ i j k,
      res M (inf_le_left : (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)) ⊓
          PrimeSpectrum.basicOpen (f k) ≤ _)
          (c i j) +
        res M (inf_le_inf inf_le_right le_rfl) (c j k) =
        res M (inf_le_inf inf_le_left le_rfl) (c i k)) :
    ∃ t : ∀ i, Section M (PrimeSpectrum.basicOpen (f i)), ∀ i j,
      res M (inf_le_right : PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j) ≤ _)
          (t j) -
        res M inf_le_left (t i) = c i j := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨N, t, ht⟩ := exists_uniform_cocycle_numerators M f c hc
  have hspan : Ideal.span (Set.range (fun k => f k ^ N)) = ⊤ := by
    simpa only [← Set.range_comp, Function.comp_def] using
      Ideal.span_pow_eq_top (Set.range f) (iSup_basicOpen_eq_top_iff.mp hcover) N
  have hone : (1 : R) ∈ Ideal.span (Set.range (fun k => f k ^ N)) := by
    rw [hspan]
    trivial
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
  refine ⟨fun i => -∑ k, a k • t i k, fun i j => ?_⟩
  simp only [map_neg, map_sum, LinearMap.map_smul]
  calc
    -(∑ k, a k • res M inf_le_right (t j k)) -
        -(∑ k, a k • res M inf_le_left (t i k)) =
      ∑ k, a k • (res M inf_le_left (t i k) - res M inf_le_right (t j k)) := by
        simp only [smul_sub, Finset.sum_sub_distrib]
        abel
    _ = ∑ k, (a k * f k ^ N) • c i j := by
      simp only [ht, mul_smul]
    _ = c i j := by rw [← Finset.sum_smul, ha, one_smul]

end AlgebraicGeometry.Scheme.Modules.AffineCech
