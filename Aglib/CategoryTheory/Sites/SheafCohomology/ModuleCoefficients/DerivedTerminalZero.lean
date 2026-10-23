/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedZeroPacket

/-!
# Original H⁰ sections in the derived module comparison

The input is the native degree-zero unit applied to an original terminal
section. The output is the original degree-zero Ext class of that section.
-/

@[expose] public noncomputable section

universe u v r w e s

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T) (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [EnoughInjectives (SheafOfModules.{max u v r w} R)]
  [HasExt.{e} (SheafOfModules.{max u v r w} R)]

/-- The native module-section unit is the original rank-one-module section class. -/
lemma derivedTerminalSectionsExtAddEquiv_zero
    (M : SheafOfModules.{max u v r w} R) (x : M.val.obj (op T)) :
    derivedTerminalSectionsExtAddEquiv.{u, v, r, w, e} hT R M 0
        ((SheafOfModules.evaluation.{max u v r w} R (op T)).toRightDerivedZero.app M x) =
      Ext.mk₀ ((liftedUnitTerminalAddEquiv.{u, v, r, w} hT R M).symm x) := by
  exact moduleRepresentedPostcomp_ext_zero_of_eq.{_, _, e, r}
    (SheafOfModules.evaluation.{max u v r w} R (op T))
    (SheafOfModules.liftedUnit.{u, v, max u v w, r} R)
    (representedTerminalSectionsIso.{u, v, r, w} hT R)
    (derivedTerminalSectionsIso.{u, v, r, w} hT R 0) rfl M x
    ((liftedUnitTerminalAddEquiv.{u, v, r, w} hT R M).symm x) rfl
    (derivedTerminalSectionsExtAddEquiv.{u, v, r, w, e} hT R M 0) rfl
    ((SheafOfModules.evaluation.{max u v r w} R (op T)).toRightDerivedZero.app M x) rfl
    (Ext.mk₀ ((liftedUnitTerminalAddEquiv.{u, v, r, w} hT R M).symm x)) rfl

variable (Λ : Type s) [Ring Λ] (α : Λ →+* R.obj.obj (op T))

/-- Actual scalar-restricted derived sections retain the same original H⁰ section. -/
lemma derivedScalarTerminalSectionsExtAddEquiv_zero
    (M : SheafOfModules.{max u v r w} R) (x : M.val.obj (op T)) :
    derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, e, s} hT R Λ α M 0
        ((scalarTerminalSections.{u, v, r, w, s} R Λ α).toRightDerivedZero.app M x) =
      Ext.mk₀ ((liftedUnitTerminalAddEquiv.{u, v, r, w} hT R M).symm x) := by
  unfold derivedScalarTerminalSectionsExtAddEquiv derivedScalarTerminalSectionsIso
  exact (scalarPostcomp_addEquiv_zero
    (SheafOfModules.evaluation.{max u v r w} R (op T)) α M
    (derivedTerminalSectionsExtAddEquiv.{u, v, r, w, e} hT R M 0) x).trans
      (derivedTerminalSectionsExtAddEquiv_zero.{u, v, r, w, e} hT R M x)

end CategoryTheory.Sheaf.ModuleCoefficients
