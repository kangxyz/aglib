/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Filtration.Pullback
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.ChosenFamily
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Proper acyclic extensions with a small acyclic quotient

Every proper acyclic subcomplex of an acyclic complex admits a strictly
larger acyclic subcomplex whose quotient is a member of the constructed
small acyclic family. The maps are the native cokernel pullback maps.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G)

include hG

omit [IsGrothendieckAbelian.{w} C] in
/-- A nonzero complex has a nonzero map from the separator into some term. -/
lemma exists_nonzero_separator_map (M : CochainComplex C ℤ) (hM : ¬ IsZero M) :
    ∃ (n : ℤ) (ψ : G ⟶ M.X n), ψ ≠ 0 := by
  classical
  by_contra! h
  apply hM
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.Hom.ext
  funext n
  change 𝟙 (M.X n) = 0
  apply hG.def _ _
  intro ψ
  simpa using h n ψ

/-- A proper acyclic inclusion has a strictly larger acyclic intermediate
complex with quotient isomorphic to a member of the fixed small family. -/
lemma exists_small_acyclic_extension {A M : CochainComplex C ℤ}
    (a : A ⟶ M) [Mono a] (hA : A.Acyclic) (hM : M.Acyclic) (ha : ¬ IsIso a) :
    ∃ (i : smallAcyclicFamilyIndex hG) (B : CochainComplex C ℤ)
      (u : A ⟶ B) (b : B ⟶ M),
      Mono u ∧ Mono b ∧ u ≫ b = a ∧ B.Acyclic ∧ ¬ IsIso u ∧
      Nonempty (cokernel u ≅ smallAcyclicFamily hG i) := by
  have hS : (ShortComplex.cokernelSequence a).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact a
      mono_f := inferInstanceAs (Mono a)
      epi_g := inferInstanceAs (Epi (cokernel.π a)) }
  have hqi : QuasiIso a := (quasiIso_iff a).2
    (fun n ↦ (quasiIsoAt_iff_exactAt a n (hA n)).2 (hM n))
  have hQ : (cokernel a).Acyclic := hS.acyclic_X₃ hqi
  have hnQ : ¬ IsZero (cokernel a) := by
    intro hz
    have : Epi a := Abelian.epi_of_cokernel_π_eq_zero a (hz.eq_of_tgt _ _)
    exact ha (isIso_of_mono_of_epi a)
  obtain ⟨n, ψ, hψ⟩ := exists_nonzero_separator_map hG (cokernel a) hnQ
  obtain ⟨i, j, t, hj, ht⟩ := smallAcyclicFamily_factorization hG _ hQ n ψ
  have : Mono j := HomologicalComplex.mono_of_mono_f j hj
  let u := ShortComplex.quotientPullbackInclusion a j
  let b := pullback.fst (cokernel.π a) j
  have hshort := ShortComplex.quotientPullbackSequence_shortExact a j
  have hR := smallAcyclicFamily_acyclic hG i
  refine ⟨i, pullback (cokernel.π a) j, u, b, inferInstance, inferInstance,
    ShortComplex.quotientPullbackInclusion_fst a j, hshort.acyclic_X₂ hA hR, ?_,
    ⟨ShortComplex.quotientPullbackCokernelIso a j⟩⟩
  intro hu
  have := hu
  have hs : pullback.snd (cokernel.π a) j = 0 := by
    apply (cancel_epi u).1
    simp [u]
  have hzero : j = 0 := by
    apply (cancel_epi (pullback.snd (cokernel.π a) j)).1
    simp [hs]
  apply hψ
  rw [← ht, hzero]
  simp

end CochainComplex
