/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.ShiftedHom

/-! Original postcomposition under shifted adjunction. -/

open CategoryTheory

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.CommShift M]

/-- The original shifted adjunction transports postcomposition through its right functor. -/
theorem shiftedHomEquiv_postcomp {I : C} {K K' : D} {r s t : M}
    (x : ShiftedHom (L.obj I) K r) (y : ShiftedHom K K' s) (h : s + r = t) :
    adj.shiftedHomEquiv t I K' (x.comp y h) =
      (adj.shiftedHomEquiv r I K x).comp (y.map R) h := by
  have hunit {W : D} {d : M} (f : ShiftedHom (L.obj I) W d) :
      adj.shiftedHomEquiv d I W f = adj.unit.app I ≫ f.map R := by
    rw [adj.shiftedHomEquiv_apply, adj.homEquiv_unit, ShiftedHom.map, Category.assoc]
  rw [hunit, hunit, ShiftedHom.map_comp]
  simp only [ShiftedHom.comp, Category.assoc]

end CategoryTheory.Adjunction
