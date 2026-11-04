/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Ext
public import Aglib.CategoryTheory.Adjunction.ShiftedHom.Contraction

/-! The trace value of the original shifted Ext product. -/

open CategoryTheory CategoryTheory.Abelian

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [HasShift C ℤ] [Category* D] [Abelian D]
  [HasDerivedCategory D] [HasExt D]
  {L : C ⥤ DerivedCategory.Plus D} {R : DerivedCategory.Plus D ⥤ C}
  (adj : L ⊣ R) [R.CommShift ℤ]

/-- The original degree-three Ext product computes the contracted value
through its two original factor equalities. -/
theorem ext_contraction_value {I : C} {U N : D}
    (u : L.obj I ⟶ (DerivedCategory.Plus.singleFunctor D 0).obj U)
    (a : Ext U U 1) (b c : Ext U N 2) (r : Ext N N 1)
    (hc : a.comp c (rfl : 1 + 2 = 3) = a.comp b (rfl : 1 + 2 = 3))
    (hr : a.comp c (rfl : 1 + 2 = 3) = c.comp r (rfl : 2 + 1 = 3))
    (τ : ShiftedHom (R.obj ((DerivedCategory.Plus.singleFunctor D 0).obj N)) I (-2 : ℤ))
    (v : ShiftedHom I I (1 : ℤ))
    (hv : (adj.shiftedHomEquiv 3 I ((DerivedCategory.Plus.singleFunctor D 0).obj N)
      (u ≫ (a.comp b (rfl : 1 + 2 = 3)).homPlus)).comp τ (by omega) = v) :
    (adj.shiftedHomEquiv 2 I ((DerivedCategory.Plus.singleFunctor D 0).obj N)
      (u ≫ c.homPlus)).comp ((r.homPlus.map R).comp τ (by omega : (-2 : ℤ) + 1 = -1))
        (by omega) = v := by
  let y := (a.comp b (rfl : 1 + 2 = 3)).homPlus
  have hy : y = c.homPlus.comp r.homPlus (by omega : (1 : ℤ) + 2 = 3) :=
    (congrArg Ext.homPlus (hc.symm.trans hr)).trans (Ext.homPlus_comp c r rfl)
  exact adj.shiftedHomEquiv_contraction_value u c.homPlus r.homPlus y
    (by omega : (1 : ℤ) + 2 = 3) hy τ (by omega : (-2 : ℤ) + 1 = -1)
    (by omega : (-2 : ℤ) + 1 + 2 = 1) v hv

end CategoryTheory.Adjunction
