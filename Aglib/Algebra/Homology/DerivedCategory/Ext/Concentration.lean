/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.ZMod.Dual
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Actual Ext concentration from uniform presentations

An exact coefficient functor and its original exact degree-zero carriers and maps
retain their given objects and arrows. Naturality of the given degree-two
adjoint and presentations by the given powers suffice for concentration and
bijectivity. The proof establishes degree-zero and degree-one vanishing
uniformly before using them on a presentation kernel. It uses self-injectivity
of the original positive ZMod ring only to extend linear functionals.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe uC vC uA vA wA wH uI

namespace CategoryTheory.Abelian.Ext

/-- Uniform presentations by the given powers give actual Ext concentration
in degree two and bijectivity of the original natural adjoint. Exactness uses
the original mapped coefficient complex and degree-zero function rows; no
additional bundled functor, replacement Ext or duality object is constructed. -/
theorem concentration_of_uniform_presentations
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{wA} A]
    (J : C ⥤ A) [J.Additive] (N : A) (n : ℕ) (hn : 0 < n)
    (H : C → Type wH) [∀ M, AddCommGroup (H M)] [∀ M, Module (ZMod n) (H M)]
    (Hmap : ∀ {M M' : C}, (M ⟶ M') → H M →ₗ[ZMod n] H M')
    (hJ : ∀ (S : ShortComplex C), S.ShortExact → (S.map J).ShortExact)
    (hH : ∀ (S : ShortComplex C), S.ShortExact →
      Function.Injective (Hmap S.f) ∧ Function.Exact (Hmap S.f) (Hmap S.g) ∧
        Function.Surjective (Hmap S.g))
    (P : C → Prop) {I : Type uI} (B : I → C)
    (hP : ∀ M, P M → ∃ (m : I) (f : B m ⟶ M), Epi f ∧ P (kernel f))
    (ν : ∀ M, Ext.{wA} (J.obj M) N 2 →+ Module.Dual (ZMod n) (H M))
    (hν : ∀ {M M' : C} (f : M ⟶ M') (e : Ext.{wA} (J.obj M') N 2) (c : H M),
      ν M ((Ext.mk₀ (J.map f)).comp e (zero_add 2)) c = ν M' e (Hmap f c))
    (hB : ∀ m q, q ≠ 2 → Subsingleton (Ext.{wA} (J.obj (B m)) N q))
    (hνB : ∀ m, Function.Bijective (ν (B m))) :
    (∀ M, P M → Function.Bijective (ν M)) ∧
      ∀ M, P M → ∀ q, q ≠ 2 → Subsingleton (Ext.{wA} (J.obj M) N q) := by
  have hν' {M M' : C} (f : M ⟶ M') (e : Ext.{wA} (J.obj M') N 2) :
      ν M ((Ext.mk₀ (J.map f)).comp e (zero_add 2)) = (Hmap f).dualMap (ν M' e) := by
    ext c
    exact hν f e c
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hzero (M : C) (hM : P M) : Subsingleton (Ext.{wA} (J.obj M) N 0) := by
    obtain ⟨m, f, hf, _⟩ := hP M hM
    let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have hS : S.ShortExact := {
      exact := by
        simpa only [S, ShortComplex.kernelSequence] using ShortComplex.kernelSequence_exact f
      epi_g := hf }
    have hJS := hJ S hS
    dsimp only [ShortComplex.map] at hJS
    let : Epi (J.map f) := hJS.epi_g
    let := hB m 0 (by decide)
    exact (Ext.precomp_mk₀_injective_of_epi N (J.map f)).subsingleton
  have hone (M : C) (hM : P M) : Subsingleton (Ext.{wA} (J.obj M) N 1) := by
    obtain ⟨m, f, hf, hK⟩ := hP M hM
    let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have hS : S.ShortExact := {
      exact := by
        simpa only [S, ShortComplex.kernelSequence] using ShortComplex.kernelSequence_exact f
      epi_g := hf }
    have hJS := hJ S hS
    dsimp only [ShortComplex.map] at hJS
    let := hB m 1 (by decide)
    let := hzero (kernel f) hK
    apply subsingleton_of_forall_eq 0
    intro e
    obtain ⟨k, hk⟩ := Ext.contravariant_sequence_exact₃ hJS N e
      (Subsingleton.elim _ _) (show 1 + 0 = 1 from rfl)
    rw [Subsingleton.elim k 0, Ext.comp_zero] at hk
    exact hk.symm
  have hinj (M : C) (hM : P M) : Function.Injective (ν M) := by
    obtain ⟨m, f, hf, hK⟩ := hP M hM
    let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have hS : S.ShortExact := {
      exact := by
        simpa only [S, ShortComplex.kernelSequence] using ShortComplex.kernelSequence_exact f
      epi_g := hf }
    have hJS := hJ S hS
    dsimp only [ShortComplex.map] at hJS
    let := hone (kernel f) hK
    apply (injective_iff_map_eq_zero _).mpr
    intro e he
    have hb : (Ext.mk₀ (J.map f)).comp e (zero_add 2) = 0 := by
      apply (hνB m).injective
      simpa only [he, map_zero] using hν' f e
    obtain ⟨k, hk⟩ := Ext.contravariant_sequence_exact₃ hJS N e hb
      (show 1 + 1 = 2 from rfl)
    rw [Subsingleton.elim k 0, Ext.comp_zero] at hk
    exact hk.symm
  have hsurj (M : C) (hM : P M) : Function.Surjective (ν M) := by
    obtain ⟨m, f, hf, hK⟩ := hP M hM
    let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have hS : S.ShortExact := {
      exact := by
        simpa only [S, ShortComplex.kernelSequence] using ShortComplex.kernelSequence_exact f
      epi_g := hf }
    have hJS := hJ S hS
    dsimp only [ShortComplex.map] at hJS
    have hHS := hH S hS
    let i := Hmap S.f
    let g := Hmap S.g
    have hg : Function.Surjective g :=
      hHS.2.2
    intro l
    obtain ⟨b, hb⟩ := (hνB m).surjective (g.dualMap l)
    have hz : i.dualMap (g.dualMap l) = 0 := by
      ext x
      change l (g (i x)) = 0
      have h : g (i x) = 0 := (hHS.2.1 (i x)).mpr ⟨x, rfl⟩
      rw [h, map_zero]
    have hk : (Ext.mk₀ (J.map S.f)).comp b (zero_add 2) = 0 := by
      apply hinj (kernel f) hK
      have h := hν' S.f b
      have hFinal := h.trans ((congrArg i.dualMap hb).trans hz)
      simpa only [map_zero] using hFinal
    obtain ⟨e, he⟩ := Ext.contravariant_sequence_exact₂ hJS N b hk
    refine ⟨e, ?_⟩
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hg y
    have h := hν' S.g e
    have hInput := congrArg (ν (B m)) he
    have hFinal := h.symm.trans (hInput.trans hb)
    exact LinearMap.congr_fun hFinal x
  have hthree (M : C) (hM : P M) : Subsingleton (Ext.{wA} (J.obj M) N 3) := by
    obtain ⟨m, f, hf, hK⟩ := hP M hM
    let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have hS : S.ShortExact := {
      exact := by
        simpa only [S, ShortComplex.kernelSequence] using ShortComplex.kernelSequence_exact f
      epi_g := hf }
    have hJS := hJ S hS
    dsimp only [ShortComplex.map] at hJS
    have hHS := hH S hS
    let i := Hmap S.f
    have hi : Function.Injective i :=
      hHS.1
    let := hB m 3 (by decide)
    apply subsingleton_of_forall_eq 0
    intro e
    obtain ⟨k, hk⟩ := Ext.contravariant_sequence_exact₃ hJS N e
      (Subsingleton.elim _ _) (show 1 + 2 = 3 from rfl)
    obtain ⟨l, hl⟩ := ZMod.dualMap_surjective n i hi (ν (kernel f) k)
    obtain ⟨b, hb⟩ := (hνB m).surjective l
    have hbK : (Ext.mk₀ (J.map S.f)).comp b (zero_add 2) = k := by
      apply hinj (kernel f) hK
      have h := hν' S.f b
      exact h.trans ((congrArg i.dualMap hb).trans hl)
    rw [← hbK, ShortComplex.ShortExact.extClass_comp_assoc] at hk
    exact hk.symm
  have hhigh : ∀ q, 3 ≤ q → ∀ M, P M →
      Subsingleton (Ext.{wA} (J.obj M) N q) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro hq M hM
      by_cases hq3 : q = 3
      · subst q
        exact hthree M hM
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      obtain ⟨m, f, hf, hK⟩ := hP M hM
      let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
      have hS : S.ShortExact := {
        exact := by
          simpa only [S, ShortComplex.kernelSequence] using ShortComplex.kernelSequence_exact f
        epi_g := hf }
      have hJS := hJ S hS
      dsimp only [ShortComplex.map] at hJS
      let := hB m (r + 1) (by omega)
      let := ih r (by omega) (by omega) (kernel f) hK
      apply subsingleton_of_forall_eq 0
      intro e
      obtain ⟨k, hk⟩ := Ext.contravariant_sequence_exact₃ hJS N e
        (Subsingleton.elim _ _) (show 1 + r = r + 1 by omega)
      rw [Subsingleton.elim k 0, Ext.comp_zero] at hk
      exact hk.symm
  refine ⟨fun M hM => ⟨hinj M hM, hsurj M hM⟩, ?_⟩
  intro M hM q hq
  by_cases hq0 : q = 0
  · subst q
    exact hzero M hM
  by_cases hq1 : q = 1
  · subst q
    exact hone M hM
  exact hhigh q (by omega) M hM

end CategoryTheory.Abelian.Ext
