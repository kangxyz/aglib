/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# All-degree Hom-complex acyclicity from shifted nullhomotopies

The existing homology/cohomology-class/homotopy-category equivalences detect
every degree. Source shifts are transported by the original shift adjunction.
This is a supplier for small-acyclic detection, not a claim that degree-zero
vanishing alone makes a Hom complex acyclic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (K I : CochainComplex C ℤ)

/-- Nullhomotopies into every target shift annihilate every native Hom-complex homology group. -/
theorem acyclic_of_nullhomotopic_target_shifts
    (h : ∀ (n : ℤ) (f : K ⟶ I⟦n⟧), Nonempty (Homotopy f 0)) :
    (HomComplex K I).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hz (x : (HomComplex K I).homology n) : x = 0 := by
    apply (homologyAddEquiv K I n).injective
    apply (CohomologyClass.homAddEquiv (K := K) (L := I) (n := n)).injective
    simp only [map_zero]
    obtain ⟨f, hf⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective
      ((CohomologyClass.homAddEquiv (homologyAddEquiv K I n x)))
    rw [← hf, HomotopyCategory.quotient_map_eq_zero_iff]
    exact h n f
  have : Subsingleton ((HomComplex K I).homology n) :=
    ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Detection on every source shift, as supplied by a genuinely shift-closed test family. -/
theorem acyclic_of_nullhomotopic_source_shifts
    (h : ∀ (a : ℤ) (f : K⟦a⟧ ⟶ I), Nonempty (Homotopy f 0)) :
    (HomComplex K I).Acyclic := by
  let Q := HomotopyCategory.quotient C (.up ℤ)
  have hq (a : ℤ) (g : Q.obj (K⟦a⟧) ⟶ Q.obj I) : g = 0 := by
    obtain ⟨f, rfl⟩ := Q.map_surjective g
    exact (HomotopyCategory.quotient_map_eq_zero_iff f).mpr (h a f)
  have hs (a : ℤ) (g : (Q.obj K)⟦a⟧ ⟶ Q.obj I) : g = 0 := by
    apply (cancel_epi ((Q.commShiftIso a).hom.app K)).1
    simpa using hq a ((Q.commShiftIso a).hom.app K ≫ g)
  apply acyclic_of_nullhomotopic_target_shifts K I
  intro n f
  let adj := (shiftEquiv' (HomotopyCategory C (.up ℤ)) (-n) n (neg_add_cancel n)).toAdjunction
  let b : Q.obj K ⟶ (Q.obj I)⟦n⟧ := Q.map f ≫ (Q.commShiftIso n).hom.app I
  have hb : b = 0 := by
    apply (adj.homEquiv (Q.obj K) (Q.obj I)).symm.injective
    exact (hs (-n) ((adj.homEquiv (Q.obj K) (Q.obj I)).symm b)).trans
      (hs (-n) ((adj.homEquiv (Q.obj K) (Q.obj I)).symm 0)).symm
  apply (HomotopyCategory.quotient_map_eq_zero_iff f).mp
  apply (cancel_mono ((Q.commShiftIso n).hom.app I)).1
  simpa [b] using hb

end CochainComplex.HomComplex
