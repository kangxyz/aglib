/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.CategoryTheory.Shift.Localization

/-!
# Shift stability of actual bounded-below quasi-isomorphisms

The original quasi-isomorphism property is stable under the native integer
shifts on bounded-below complexes. The fully faithful inclusion's original
shift comparison identifies its mapped arrow with the shifted unbounded
arrow. This supplies the localization hypothesis for original derived
descent comparisons without altering the induced shift structure.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CochainComplex.Plus

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Native integer shifts preserve and reflect the original bounded-below
quasi-isomorphisms. -/
instance quasiIso_isCompatibleWithShift : (quasiIso C).IsCompatibleWithShift ℤ where
  condition n := by
    ext K L f
    change (HomologicalComplex.quasiIso C (.up ℤ)) ((f⟦n⟧').hom) ↔
      (HomologicalComplex.quasiIso C (.up ℤ)) f.hom
    rw [← MorphismProperty.IsCompatibleWithShift.iff
      (HomologicalComplex.quasiIso C (.up ℤ)) f.hom n]
    exact (HomologicalComplex.quasiIso C (.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoOfNatIso ((ι C).commShiftIso n) (Arrow.mk f))

end CochainComplex.Plus
