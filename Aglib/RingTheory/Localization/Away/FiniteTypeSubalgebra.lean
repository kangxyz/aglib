/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.Away.MapInverse
public import Mathlib.RingTheory.FiniteType

/-!
# Finite numerator selection in a finite-type principal localization

Only the localization is assumed finite type over the coefficient ring.
Its original ring need not be finitely generated. Finitely many numerators
suffice, together with the distinguished inverse, to generate the localization.
-/

@[expose] public section

noncomputable section

namespace IsLocalization.Away

variable {R A S : Type*} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra A S] [Algebra R S] [IsScalarTower R A S]

omit [Algebra R A] [IsScalarTower R A S] in
/-- Finite generation of a principal localization can be witnessed by finitely
many original numerators and the inverse of the original denominator. -/
theorem exists_finset_numerators (f : A) [IsLocalization.Away f S]
    [Algebra.FiniteType R S] :
    ∃ t : Finset A, f ∈ t ∧
      Algebra.adjoin R ((algebraMap A S '' (t : Set A)) ∪ {invSelf f}) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R S).out
  let t := insert f (s.image fun z => (sec f z).1)
  refine ⟨t, Finset.mem_insert_self _ _, top_unique ?_⟩
  rw [← hs]
  apply Algebra.adjoin_le
  intro z hz
  have ha : algebraMap A S (sec f z).1 ∈
      Algebra.adjoin R ((algebraMap A S '' (t : Set A)) ∪ {invSelf f}) :=
    Algebra.subset_adjoin (Or.inl ⟨_, Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨z, hz, rfl⟩), rfl⟩)
  have hi : (invSelf f : S) ∈
      Algebra.adjoin R ((algebraMap A S '' (t : Set A)) ∪ {invSelf f}) :=
    Algebra.subset_adjoin (Or.inr rfl)
  have he : z = algebraMap A S (sec f z).1 * (invSelf f : S) ^ (sec f z).2 := by
    rw [← sec_spec f z, map_pow, mul_assoc, ← mul_pow, mul_invSelf, one_pow, mul_one]
  rw [he]
  exact mul_mem ha (pow_mem hi _)

/-- Any subalgebra containing the selected numerators maps surjectively onto
the principal localization after inverting the same denominator. -/
theorem subalgebra_map_surjective_of_numerators (f : A) [IsLocalization.Away f S]
    (t : Finset A)
    (ht : Algebra.adjoin R ((algebraMap A S '' (t : Set A)) ∪ {invSelf f}) = ⊤)
    (B : Subalgebra R A) (hf : f ∈ B) (hB : ∀ a ∈ t, a ∈ B) :
    let _ : IsLocalization.Away (B.val ⟨f, hf⟩) S := ‹IsLocalization.Away f S›
    Function.Surjective
      (mapₐ (Localization.Away (⟨f, hf⟩ : B)) S B.val ⟨f, hf⟩) := by
  let : IsLocalization.Away (B.val ⟨f, hf⟩) S := ‹IsLocalization.Away f S›
  let φ := mapₐ (Localization.Away (⟨f, hf⟩ : B)) S B.val ⟨f, hf⟩
  have hpow : Submonoid.powers (⟨f, hf⟩ : B) ≤
      (Submonoid.powers f).comap B.val.toRingHom := by
    rintro a ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  have hφ (a : B) : φ (algebraMap B _ a) = algebraMap A S a.val :=
    IsLocalization.map_eq (T := Submonoid.powers f) hpow a
  apply (AlgHom.range_eq_top φ).mp
  apply top_unique
  rw [← ht]
  apply Algebra.adjoin_le
  rintro z (⟨a, ha, rfl⟩ | rfl)
  · refine ⟨algebraMap B _ ⟨a, hB a ha⟩, ?_⟩
    exact hφ _
  · refine ⟨invSelf (⟨f, hf⟩ : B), ?_⟩
    apply Localization.Away.map_invSelf_of_mul
    rw [show φ.toRingHom (algebraMap B _ ⟨f, hf⟩) = algebraMap A S f from
      hφ _]
    exact mul_invSelf f

end IsLocalization.Away

namespace IsLocalization.Away

variable {K A ι : Type*} [CommRing K] [CommRing A] [Algebra K A] [Finite ι]

/-- Finitely many finite-type principal localizations are already unchanged
over one finitely generated coefficient subalgebra containing any prescribed
finite set. The comparison maps are the actual localized inclusions. -/
theorem exists_fg_subalgebra_localization_bijective (g : ι → A)
    [∀ i, Algebra.FiniteType K (Localization.Away (g i))] (q : Finset A) :
    ∃ B : Subalgebra K A, B.FG ∧ (∀ a ∈ q, a ∈ B) ∧
      ∃ hg : ∀ i, g i ∈ B, ∀ i,
        let _ : IsLocalization.Away (B.val ⟨g i, hg i⟩)
            (Localization.Away (g i)) :=
          inferInstanceAs (IsLocalization.Away (g i) (Localization.Away (g i)))
        Function.Bijective
          (mapₐ (Localization.Away (⟨g i, hg i⟩ : B))
            (Localization.Away (g i)) B.val ⟨g i, hg i⟩) := by
  classical
  let _ := Fintype.ofFinite ι
  choose t htg ht using fun i =>
    exists_finset_numerators (R := K) (S := Localization.Away (g i)) (g i)
  let q' := q ∪ Finset.univ.biUnion t
  let B := Algebra.adjoin K (q' : Set A)
  have htB (i : ι) (a : A) (ha : a ∈ t i) : a ∈ B := by
    apply Algebra.subset_adjoin
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩)
  have hg (i : ι) : g i ∈ B := htB i _ (htg i)
  refine ⟨B, Subalgebra.fg_adjoin_finset _, ?_, hg, ?_⟩
  · intro a ha
    exact Algebra.subset_adjoin (Finset.mem_union_left _ ha)
  · intro i
    let _ : IsLocalization.Away (B.val ⟨g i, hg i⟩) (Localization.Away (g i)) :=
      inferInstanceAs (IsLocalization.Away (g i) (Localization.Away (g i)))
    constructor
    · exact mapₐ_injective_of_injective
        (Aₚ := Localization.Away (⟨g i, hg i⟩ : B))
        (Bₚ := Localization.Away (g i)) (f := B.val) ⟨g i, hg i⟩
        Subtype.val_injective
    · exact subalgebra_map_surjective_of_numerators
        (g i) (t i) (ht i) B (hg i) (htB i)

end IsLocalization.Away
