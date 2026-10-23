/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedGamma
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Actual scalar-valued terminal sections

The coefficient ring acts by its given homomorphism into terminal sections of
the ring sheaf. In particular, for a constant ring sheaf this homomorphism is
the original constant-sheaf adjunction unit. No equality between the constant
coefficient ring and all global sections of its sheaf is assumed.
-/

@[expose] public noncomputable section

universe u v r w e s

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T) (R : Sheaf J RingCat.{r})
  (Λ : Type s) [Ring Λ] (α : Λ →+* R.obj.obj (op T))

/-- Actual terminal sections with scalars restricted along the coefficient action. -/
def scalarTerminalSections : SheafOfModules.{max u v r w} R ⥤ ModuleCat.{max u v r w} Λ :=
  SheafOfModules.evaluation.{max u v r w} R (op T) ⋙ ModuleCat.restrictScalars.{max u v r w} α

instance : (scalarTerminalSections.{u, v, r, w, s} R Λ α).Additive :=
  inferInstanceAs ((SheafOfModules.evaluation.{max u v r w} R (op T) ⋙
    ModuleCat.restrictScalars.{max u v r w} α).Additive)

instance : (ModuleCat.restrictScalars.{max u v r w} α).PreservesHomology where

variable [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [EnoughInjectives (SheafOfModules.{max u v r w} R)]

/-- Scalar restriction commutes with native right-derived terminal sections. -/
def derivedScalarTerminalSectionsIso (n : ℕ) :
    (scalarTerminalSections R Λ α).rightDerived n ≅
      (SheafOfModules.evaluation.{max u v r w} R (op T)).rightDerived n ⋙
        ModuleCat.restrictScalars.{max u v r w} α :=
  rightDerivedPostcompIso _ _ n

variable [HasExt.{e} (SheafOfModules.{max u v r w} R)]

/-- The underlying additive group of actual coefficient-valued derived sections
is the original represented Ext. -/
def derivedScalarTerminalSectionsExtAddEquiv
    (M : SheafOfModules.{max u v r w} R) (n : ℕ) :
    ((scalarTerminalSections R Λ α).rightDerived n).obj M ≃+
      Ext.{e} (SheafOfModules.liftedUnit.{u, v, max u v w, r} R) M n :=
  scalarDerivedModuleAddEquiv
    ((SheafOfModules.evaluation.{max u v r w} R (op T)).rightDerived n)
    ((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n) α
    (derivedScalarTerminalSectionsIso.{u, v, r, w, s} R Λ α n) M
    (derivedTerminalSectionsExtAddEquiv.{u, v, r, w, e} hT R M n)

section Constant

variable [HasSheafify J RingCat.{r}] (A : RingCat.{r})

/-- The canonical coefficient action on global sections of a constant ring sheaf. -/
def constantTerminalScalarHom :
    A →+* (((constantSheaf J RingCat).obj A).obj.obj (op T)) :=
  ((constantSheafAdj J RingCat hT).unit.app A).hom

/-- Original global sections with the original constant coefficient ring action. -/
def constantTerminalSections :
    SheafOfModules.{max u v r w} ((constantSheaf J RingCat).obj A) ⥤
      ModuleCat.{max u v r w} A :=
  scalarTerminalSections _ A (constantTerminalScalarHom hT A)

instance : (constantTerminalSections.{u, v, r, w} (J := J) hT A).Additive :=
  inferInstanceAs
    (scalarTerminalSections.{u, v, r, w, r} _ A (constantTerminalScalarHom (J := J) hT A)).Additive

end Constant

end CategoryTheory.Sheaf.ModuleCoefficients
