/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Charts


/-!
# The two original parameter charts cover the same original blowup

The original two elements of the supplied ideal select a subfamily of its
native affine atlas. The native generator-cover theorem proves that this
subfamily covers the entire original blowup, not only its exceptional fibre.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Blowup.RegularPoint

universe u

namespace AlgebraicGeometry.Scheme.Blowup.PairIdeal

variable {R : Type u} [CommRing R] (I : Ideal R) (x y : R)
  (hI : Ideal.span {x, y} = I)

/-- The two original generators as actual elements of the same supplied ideal. -/
def pairIdealGenerator (i : Bool) : I :=
  if i then firstGenerator I x y hI else
    firstGenerator I y x (Ideal.span_pair_comm.trans hI)

/-- The native original saturated chart schemes for this two-element subfamily. -/
abbrev pairIdealChartScheme (i : Bool) : Scheme.{u} :=
  Spec (.of (Blowup.affineBlowupAlgebra R I (pairIdealGenerator I x y hI i)))

/-- The original atlas arrow, without any replacement blowup. -/
abbrev pairIdealChart (i : Bool) : pairIdealChartScheme I x y hI i ⟶ canonicalBlowup I :=
  (Blowup.affineAtlas (Blowup.blowupDatum (Blowup.affineCenter R I))).chart
    (pairIdealGenerator I x y hI i)

instance pairIdealChart_isOpenImmersion (i : Bool) :
    IsOpenImmersion (pairIdealChart I x y hI i) :=
  (Blowup.affineAtlas (Blowup.blowupDatum (Blowup.affineCenter R I))).openImmersion _

/-- Both parameter charts cover the entire original blowup. -/
theorem pairIdealCharts_cover (z : canonicalBlowup I) :
    ∃ (i : Bool) (w : pairIdealChartScheme I x y hI i), pairIdealChart I x y hI i w = z := by
  have hg : Ideal.span (Set.range (fun i => (pairIdealGenerator I x y hI i : R))) = I := by
    have hr : Set.range (fun i => (pairIdealGenerator I x y hI i : R)) = {x, y} := by
      ext t
      constructor
      · rintro ⟨i, rfl⟩
        cases i <;> simp [pairIdealGenerator, firstGenerator]
      · intro ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
        rcases ht with h | h
        · subst t
          exact ⟨true, rfl⟩
        · subst t
          exact ⟨false, rfl⟩
    exact (congrArg Ideal.span hr).trans hI
  obtain ⟨i, w, hw⟩ :=
    (Blowup.affineAtlas (Blowup.blowupDatum (Blowup.affineCenter R I))).generator_covers
      (pairIdealGenerator I x y hI) hg z
  exact ⟨i, w, hw⟩

end AlgebraicGeometry.Scheme.Blowup.PairIdeal
