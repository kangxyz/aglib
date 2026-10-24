/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Filtration.SubobjectStep
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.ShiftFamily

/-!
# The inflationary acyclic growth operator

The operator is defined on the entire native subobject lattice. Nonacyclic
inputs are sent to the top subobject; this makes a total inflationary operator
without asserting that arbitrary joins of acyclic subobjects are acyclic.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G) (M : CochainComplex C ℤ) (hM : M.Acyclic)

/-- A total inflationary operator, with the actual small-quotient successor
on proper acyclic subobjects and an explicit top branch elsewhere. -/
def acyclicGrowth (A : Subobject M) : Subobject M := by
  classical
  exact if htop : A = ⊤ then A else
    if hA : (A : CochainComplex C ℤ).Acyclic then
      (exists_small_acyclic_subobject_step hG M hM A hA htop).choose
    else ⊤

@[simp]
lemma acyclicGrowth_top : acyclicGrowth hG M hM ⊤ = ⊤ := by
  simp [acyclicGrowth]

lemma lt_acyclicGrowth (A : Subobject M) (hne : A ≠ ⊤) :
    A < acyclicGrowth hG M hM A := by
  classical
  by_cases hA : (A : CochainComplex C ℤ).Acyclic
  · rw [acyclicGrowth, dite_eq_right hne, dite_eq_left hA]
    exact (exists_small_acyclic_subobject_step hG M hM A hA hne).choose_spec.choose
  · rw [acyclicGrowth, dite_eq_right hne, dite_eq_right hA]
    exact lt_top_iff_ne_top.2 hne

lemma le_acyclicGrowth (A : Subobject M) : A ≤ acyclicGrowth hG M hM A := by
  by_cases h : A = ⊤
  · subst A
    rw [acyclicGrowth_top]
  · exact (lt_acyclicGrowth hG M hM A h).le

lemma acyclicGrowth_acyclic (A : Subobject M)
    (hA : (A : CochainComplex C ℤ).Acyclic) :
    (acyclicGrowth hG M hM A : CochainComplex C ℤ).Acyclic := by
  classical
  by_cases htop : A = ⊤
  · simpa only [acyclicGrowth, dite_eq_left htop] using hA
  · rw [acyclicGrowth, dite_eq_right htop, dite_eq_left hA]
    obtain ⟨hlt, i, hi, hq⟩ :=
      (exists_small_acyclic_subobject_step hG M hM A hA htop).choose_spec
    exact hi

/-- Every proper acyclic step has its canonical quotient in the one final
shift-closed test family, through the specified zero-shift comparison. -/
lemma acyclicGrowth_quotient (A : Subobject M)
    (hA : (A : CochainComplex C ℤ).Acyclic) (hne : A ≠ ⊤) :
    ∃ i : smallAcyclicTestIndex hG,
      Nonempty (cokernel (Subobject.ofLE A (acyclicGrowth hG M hM A)
        (le_acyclicGrowth hG M hM A)) ≅ smallAcyclicTests hG i) := by
  classical
  let B := (exists_small_acyclic_subobject_step hG M hM A hA hne).choose
  obtain ⟨hlt, i, hi, ⟨e⟩⟩ :=
    (exists_small_acyclic_subobject_step hG M hM A hA hne).choose_spec
  have hB : acyclicGrowth hG M hM A = B := by
    simp only [acyclicGrowth, dite_eq_right hne, dite_eq_left hA, B]
  let eB := Subobject.isoOfEq (acyclicGrowth hG M hM A) B hB
  refine ⟨(i, 0), ⟨(cokernel.mapIso
    (Subobject.ofLE A (acyclicGrowth hG M hM A) (le_acyclicGrowth hG M hM A))
    (Subobject.ofLE A B hlt.le) (Iso.refl _) eB ?_) ≪≫ e ≪≫
      (smallAcyclicTestsZeroIso hG i).symm⟩⟩
  apply (cancel_mono B.arrow).1
  simp only [eB, Subobject.isoOfEq, Category.assoc, Subobject.ofLE_arrow,
    Iso.refl_hom, Category.id_comp]

end CochainComplex
