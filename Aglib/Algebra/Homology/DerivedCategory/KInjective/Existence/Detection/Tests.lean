/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.ShiftFamily
public import Aglib.Algebra.Homology.HomComplex.ShiftDetection
public import Aglib.Algebra.Homology.HomComplex.SourceIso

/-! # All-degree detection on the single shift-closed small family -/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G) (I : CochainComplex C ℤ)

/-- Nullhomotopies on the final test family annihilate every Hom-complex degree. -/
lemma smallAcyclicTests_homComplex_acyclic
    (h : ∀ i (f : smallAcyclicTests hG i ⟶ I), Nonempty (Homotopy f 0))
    (i : smallAcyclicTestIndex hG) : (HomComplex (smallAcyclicTests hG i) I).Acyclic := by
  apply HomComplex.acyclic_of_nullhomotopic_source_shifts
  intro n f
  let e := smallAcyclicTestsShiftIso hG i n
  obtain ⟨s⟩ := h (i.1, i.2 + n) (e.inv ≫ f)
  exact ⟨(Homotopy.ofEq (by simp)).trans
    ((s.compLeft e.hom).trans (Homotopy.ofEq (by simp)))⟩

end CochainComplex
