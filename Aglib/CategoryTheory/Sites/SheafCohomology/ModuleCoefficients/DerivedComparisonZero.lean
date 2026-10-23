/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedTerminalZero

/-!
# Original sections in degree zero of the derived comparison

The left hand side derives actual terminal evaluation, with actual scalar
restriction for a coefficient action. The right hand side is original
`Sheaf.H`. The comparison is obtained from genuine injective acyclicity,
not from an assumed comparison or acyclicity premise.

The left side is the literal composition defining
`derivedScalarCohomologyAddEquiv` and its large-scalar variant. Stating
normalization on the original maps avoids a redundant equivalence-alias
conversion and retains the original section unit and original abelian class.
-/

@[expose] public noncomputable section

universe u v r w eM eA s

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T) (R : Sheaf J RingCat.{r})
  (Λ : Type s) [Ring Λ] (α : Λ →+* R.obj.obj (op T))
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [EnoughInjectives (SheafOfModules.{max u v r w} R)]
  [HasExt.{eM} (SheafOfModules.{max u v r w} R)]
  [HasExt.{eA} (Sheaf J AddCommGrpCat.{max u v r w})]

/-- The original derived comparison sends the section unit to its original abelian class. -/
theorem cohomologyMap_derivedScalarSections_zero
    (M : SheafOfModules.{max u v r w} R) (x : M.val.obj (op T)) :
    cohomologyMap.{u, v, r, max u v w, eM, eA} hT R M 0
        (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, eM, s} hT R Λ α M 0
          ((scalarTerminalSections.{u, v, r, w, s} R Λ α).toRightDerivedZero.app M x)) =
      Ext.mk₀ (liftedUnitIntegerMap.{u, v, r, max u v w} hT R ≫
        (SheafOfModules.toSheaf R).map
        ((liftedUnitTerminalAddEquiv.{u, v, r, w} hT R M).symm x)) :=
  (congrArg (cohomologyMap.{u, v, r, max u v w, eM, eA} hT R M 0)
    (derivedScalarTerminalSectionsExtAddEquiv_zero.{u, v, r, w, eM, s}
      hT R Λ α M x)).trans
        (cohomologyMap_mk₀.{u, v, r, max u v w, eM, eA} hT R M
          ((liftedUnitTerminalAddEquiv.{u, v, r, w} hT R M).symm x))

end CategoryTheory.Sheaf.ModuleCoefficients
