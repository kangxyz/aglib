/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.ChosenFamily

/-!
# The fixed shift-closed small acyclic test family

This is the single final family for both map killing and detection. Its small
index includes an integer shift explicitly; no hidden representation property
of an existentially chosen family is used to claim shift closure.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian
  HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G)

/-- The final small test index includes every integer shift. -/
abbrev smallAcyclicTestIndex : Type w := smallAcyclicFamilyIndex hG × ℤ

/-- The one fixed shift-closed family used by replacement and detection. -/
def smallAcyclicTests (i : smallAcyclicTestIndex hG) : CochainComplex C ℤ :=
  (smallAcyclicFamily hG i.1)⟦i.2⟧

lemma smallAcyclicTests_acyclic (i : smallAcyclicTestIndex hG) :
    (smallAcyclicTests hG i).Acyclic := by
  intro n
  rw [exactAt_iff_isZero_homology]
  have h := (exactAt_iff_isZero_homology _ _).1
    (smallAcyclicFamily_acyclic hG i.1 (i.2 + n))
  exact IsZero.of_iso h
    (((homologyFunctor C _ (0 : ℤ)).shiftIso i.2 n _ rfl).app (smallAcyclicFamily hG i.1))

lemma smallAcyclicTests_boundedAbove (i : smallAcyclicTestIndex hG) :
    ∃ n : ℤ, (smallAcyclicTests hG i).IsStrictlyLE n := by
  obtain ⟨n, hn⟩ := smallAcyclicFamily_boundedAbove hG i.1
  have := hn
  exact ⟨n - i.2, isStrictlyLE_shift _ n i.2 (n - i.2) (by omega)⟩

lemma smallAcyclicTests_size (i : smallAcyclicTestIndex hG) (n : ℤ) :
    HasCardinalLT (Subobject ((smallAcyclicTests hG i).X n)) (smallAcyclicCardinal hG) := by
  change HasCardinalLT (Subobject (((smallAcyclicFamily hG i.1)⟦i.2⟧).X n)) _
  let e : ((smallAcyclicFamily hG i.1)⟦i.2⟧).X n ≅
      (smallAcyclicFamily hG i.1).X (i.2 + n) :=
    (smallAcyclicFamily hG i.1).shiftFunctorObjXIso i.2 n (i.2 + n) (add_comm _ _)
  exact Subobject.hasCardinalLT_of_mono (smallAcyclicFamily_size hG i.1 (i.2 + n)) e.hom

/-- Original quotient representatives are literally the zero-shift tests up to
this specified native shift-zero isomorphism. -/
def smallAcyclicTestsZeroIso (i : smallAcyclicFamilyIndex hG) :
    smallAcyclicTests hG (i, 0) ≅ smallAcyclicFamily hG i :=
  (shiftFunctorZero (CochainComplex C ℤ) ℤ).app _

/-- Every further shift is represented by addition in the fixed test index. -/
def smallAcyclicTestsShiftIso (i : smallAcyclicTestIndex hG) (n : ℤ) :
    (smallAcyclicTests hG i)⟦n⟧ ≅ smallAcyclicTests hG (i.1, i.2 + n) :=
  ((shiftFunctorAdd (CochainComplex C ℤ) i.2 n).app (smallAcyclicFamily hG i.1)).symm

end CochainComplex
