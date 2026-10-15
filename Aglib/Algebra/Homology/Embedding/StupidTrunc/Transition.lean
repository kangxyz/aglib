/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.Embedding.StupidTrunc.Maps
/-! # Actual nested brutal-truncation inclusions

The transition from a larger cutoff to a smaller cutoff is characterized by
its unchanged composite into the original complex. Its naturality and strict
composition are proved using that genuine monomorphism. Each transition is
split in every degree; no chain splitting is asserted.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace CochainComplex
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Degreewise components of the actual increasing-cutoff transition. -/
def stupidTruncGETransitionF (K : CochainComplex A ℤ) {n m : ℤ} (h : n ≤ m) (i : ℤ) :
    (stupidTruncGE K m).X i ⟶ (stupidTruncGE K n).X i :=
  if hm : m ≤ i then (stupidTruncGEXIso K m i hm).hom ≫
    (stupidTruncGEXIso K n i (h.trans hm)).inv else 0

/-- Its components have precisely the original inclusion as composite. -/
@[reassoc]
theorem stupidTruncGETransitionF_inclusion (K : CochainComplex A ℤ)
    {n m : ℤ} (h : n ≤ m) (i : ℤ) :
    stupidTruncGETransitionF K h i ≫ (stupidTruncGEInclusion K n).f i =
      (stupidTruncGEInclusion K m).f i := by
  by_cases hm : m ≤ i
  · simp [stupidTruncGETransitionF, hm, stupidTruncGEInclusion_f_of_le K n i (h.trans hm)]
  · exact (stupidTruncGE_isZero_X K m i (by omega)).eq_of_src _ _

/-- The actual chain map between nested original brutal truncations. -/
def stupidTruncGETransition (K : CochainComplex A ℤ) {n m : ℤ} (h : n ≤ m) :
    stupidTruncGE K m ⟶ stupidTruncGE K n where
  f := stupidTruncGETransitionF K h
  comm' i j _ := by
    let : IsSplitMono ((stupidTruncGEInclusion K n).f j) :=
      stupidTruncGEInclusion_degreewiseSplitMono K n j
    apply (cancel_mono ((stupidTruncGEInclusion K n).f j)).1
    rw [Category.assoc, ← (stupidTruncGEInclusion K n).comm i j,
      ← Category.assoc, stupidTruncGETransitionF_inclusion,
      Category.assoc, stupidTruncGETransitionF_inclusion]
    exact (stupidTruncGEInclusion K m).comm i j

@[reassoc (attr := simp)]
theorem stupidTruncGETransition_inclusion (K : CochainComplex A ℤ) {n m : ℤ} (h : n ≤ m) :
    stupidTruncGETransition K h ≫ stupidTruncGEInclusion K n = stupidTruncGEInclusion K m := by
  ext i
  exact stupidTruncGETransitionF_inclusion K h i

/-- Transitions are natural in the original chain map. -/
@[reassoc]
theorem stupidTruncGETransition_naturality {K L : CochainComplex A ℤ}
    (f : K ⟶ L) {n m : ℤ} (h : n ≤ m) :
    (stupidTruncGEFunctor m).map f ≫ stupidTruncGETransition L h =
      stupidTruncGETransition K h ≫ (stupidTruncGEFunctor n).map f := by
  let : Mono (stupidTruncGEInclusion L n) :=
    degreewiseSplitMono_mono (stupidTruncGEInclusion_degreewiseSplitMono L n)
  apply (cancel_mono (stupidTruncGEInclusion L n)).1
  simp only [Category.assoc, stupidTruncGETransition_inclusion,
    stupidTruncGEInclusion_naturality, stupidTruncGETransition_inclusion_assoc]

/-- The canonical transition natural transformation of the existing functors. -/
def stupidTruncGETransitionNat {n m : ℤ} (h : n ≤ m) :
    stupidTruncGEFunctor (A := A) m ⟶ stupidTruncGEFunctor n where
  app K := stupidTruncGETransition K h
  naturality _ _ f := stupidTruncGETransition_naturality f h

/-- Every actual transition is degreewise split. -/
theorem stupidTruncGETransition_degreewiseSplitMono (K : CochainComplex A ℤ)
    {n m : ℤ} (h : n ≤ m) : degreewiseSplitMono (stupidTruncGETransition K h) := by
  intro i
  by_cases hm : m ≤ i
  · change IsSplitMono (stupidTruncGETransitionF K h i)
    simp only [stupidTruncGETransitionF, dite_eq_left hm]
    infer_instance
  · exact IsSplitMono.mk' ⟨0, (stupidTruncGE_isZero_X K m i (by omega)).eq_of_src _ _⟩

/-- Identity transitions are literal identities. -/
@[simp]
theorem stupidTruncGETransition_id (K : CochainComplex A ℤ) (n : ℤ) :
    stupidTruncGETransition K (le_refl n) = 𝟙 _ := by
  let : Mono (stupidTruncGEInclusion K n) :=
    degreewiseSplitMono_mono (stupidTruncGEInclusion_degreewiseSplitMono K n)
  apply (cancel_mono (stupidTruncGEInclusion K n)).1
  simp

/-- Composition retains the original strictly compatible transition. -/
@[reassoc (attr := simp)]
theorem stupidTruncGETransition_comp (K : CochainComplex A ℤ) {l n m : ℤ}
    (h : l ≤ n) (h' : n ≤ m) :
    stupidTruncGETransition K h' ≫ stupidTruncGETransition K h =
      stupidTruncGETransition K (h.trans h') := by
  let : Mono (stupidTruncGEInclusion K l) :=
    degreewiseSplitMono_mono (stupidTruncGEInclusion_degreewiseSplitMono K l)
  apply (cancel_mono (stupidTruncGEInclusion K l)).1
  simp

end CochainComplex
