/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Unit
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Actual terminal sections represented by the lifted module unit

The original scalar ring is unchanged. The comparison identifies original
module evaluation followed by scalar forgetting with the represented
additive functor, naturally in coefficients.
-/

@[expose] public noncomputable section

universe u v r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T) (R : Sheaf J RingCat.{r})

/-- The lifted unit represents terminal sections additively over unchanged scalars. -/
def liftedUnitTerminalAddEquiv (M : SheafOfModules.{max u v r w} R) :
    (SheafOfModules.liftedUnit.{u, v, max u v w, r} R ⟶ M) ≃+ M.val.obj (op T) where
  toEquiv := liftedUnitHomTerminalEquiv (hT := hT) (R := R) M
  map_add' _ _ := rfl

/-- The represented functor is the original module evaluation followed by forgetting. -/
def representedTerminalSectionsIso :
    preadditiveCoyoneda.obj (op (SheafOfModules.liftedUnit.{u, v, max u v w, r} R)) ≅
      SheafOfModules.evaluation.{max u v r w} R (op T) ⋙
        forget₂ (ModuleCat (R.obj.obj (op T))) AddCommGrpCat :=
  NatIso.ofComponents (fun M => (liftedUnitTerminalAddEquiv hT R M).toAddCommGrpIso)
    (by
      intro M N f
      ext a
      rfl)

end CategoryTheory.Sheaf.ModuleCoefficients
