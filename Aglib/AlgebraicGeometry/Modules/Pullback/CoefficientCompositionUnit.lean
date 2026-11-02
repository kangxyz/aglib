/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitValues

/-! # Unit values of composed original coefficient maps

The complete value law combines the native equality and composition comparisons
with unit naturality, for arbitrary schemes and coefficient sheaves.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The original composite coefficient map takes a unit section to the two
successive coefficient-unit values. No coefficient regularity is required. -/
theorem pullback_coefficient_comp_unit_app_top
    {X Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ Y) (r : Z ⟶ X)
    (h : r = q ≫ p) {E : X.Modules} {F : Y.Modules} {G : Z.Modules}
    (a : (pullback p).obj E ⟶ F) (b : (pullback q).obj F ⟶ G)
    (m : Γ(E, ⊤)) :
    ((pullbackCongr h).hom.app E ≫ (pullbackComp q p).inv.app E ≫
        CategoryTheory.Functor.map (pullback q) a ≫ b).app ⊤
          (((pullbackPushforwardAdjunction r).unit.app E).app ⊤ m) =
      b.app ⊤ (((pullbackPushforwardAdjunction q).unit.app F).app ⊤
        (a.app ⊤ (((pullbackPushforwardAdjunction p).unit.app E).app ⊤ m))) := by
  change
    b.app ⊤ ((CategoryTheory.Functor.map (pullback q) a).app ⊤
      (((pullbackComp q p).inv.app E).app ⊤
        (((pullbackCongr h).hom.app E).app ⊤
          (((pullbackPushforwardAdjunction r).unit.app E).app ⊤ m)))) = _
  rw [pullbackCongr_unit_app_top, pullbackComp_inv_unit_app_top]
  have hn := pullback_unit_naturality_app_top q a
    (((pullbackPushforwardAdjunction p).unit.app E).app ⊤ m)
  exact congrArg (fun z : Γ((pullback q).obj F, ⊤) => b.app ⊤ z) hn.symm

end AlgebraicGeometry.Scheme.Modules
