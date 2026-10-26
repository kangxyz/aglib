/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Global.Comparison
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Evaluation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Terminal evaluation of intrinsic represented sections

Every terminal comparison assumes an explicit terminal object. The intrinsic
functors remain represented Hom. The site-global comparison displays the lift
from the coefficient-value universe to the sheaf-Hom universe; the original
module-valued terminal API uses its existing aligned universe.

The original `ModuleCoefficients.RepresentedSections` and `DerivedGamma` names
are transparent specializations of the constructors here.
-/

@[expose] public noncomputable section

universe u v a r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Original sheaf evaluation is the additive inclusion followed by additive evaluation. -/
instance sheafSections_additive (U : Cᵒᵖ) :
    ((sheafSections J AddCommGrpCat.{a}).obj U).Additive :=
  inferInstanceAs (Functor.Additive
    (sheafToPresheaf J AddCommGrpCat.{a} ⋙ (evaluation _ _).obj U))

variable [HasSheafify J AddCommGrpCat.{a}] {T : C} (hT : IsTerminal T)

/-- Intrinsic global sections give original terminal values without changing their universe. -/
abbrev globalGammaTerminalAddEquiv (F : Sheaf J AddCommGrpCat.{a}) :
    (globalGamma J).obj F ≃+ F.obj.obj (op T) :=
  ModuleCoefficients.integerHomTerminalEquiv hT F

/-- The terminal evaluation view, with its necessary coefficient-value lift explicit. -/
def globalGammaTerminalIso :
    globalGamma J ≅ (sheafSections J AddCommGrpCat.{a}).obj (op T) ⋙
      AddCommGrpCat.uliftFunctor.{u, a} :=
  NatIso.ofComponents
    (fun F => ((globalGammaTerminalAddEquiv hT F).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (by
      intro F G f
      ext x
      apply ULift.ext
      exact ModuleCoefficients.integerHomTerminalEquiv_comp hT x f)

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{a})]

/-- Native derived terminal evaluation compares with intrinsic derived global sections. -/
def derivedGlobalGammaTerminalIso (n : ℕ) :
    ((sheafSections J AddCommGrpCat.{a}).obj (op T)).rightDerived n ⋙
        AddCommGrpCat.uliftFunctor.{u, a} ≅
      (globalGamma J).rightDerived n :=
  Functor.representedRightDerivedPostcompIso _
    ((sheafSections J AddCommGrpCat.{a}).obj (op T))
    AddCommGrpCat.uliftFunctor.{u, a} (globalGammaTerminalIso hT) n

end CategoryTheory.Sheaf

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T) (R : Sheaf J RingCat.{r})

/-- The actual lifted-unit representation gives original terminal module sections. -/
def representedGammaTerminalAddEquiv (M : SheafOfModules.{max r w} R) :
    (representedGamma.{u, v, r, w} R).obj M ≃+ M.val.obj (op T) where
  toEquiv := CategoryTheory.Sheaf.ModuleCoefficients.liftedUnitHomTerminalEquiv
    (hT := hT) (R := R) M
  map_add' _ _ := rfl

/-- In the original aligned universe, represented sections are original module evaluation. -/
def representedGammaTerminalIso :
    representedGamma.{u, v, r, max u v w} R ≅
      evaluation.{max u v r w} R (op T) ⋙
        forget₂ (ModuleCat (R.obj.obj (op T))) AddCommGrpCat :=
  NatIso.ofComponents
    (fun M => (representedGammaTerminalAddEquiv hT R M).toAddCommGrpIso)
    (by
      intro M N f
      ext x
      rfl)

variable [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [EnoughInjectives (SheafOfModules.{max u v r w} R)]

/-- Exact scalar forgetting compares original derived evaluation with represented Gamma. -/
def derivedRepresentedGammaTerminalIso (n : ℕ) :
    (evaluation.{max u v r w} R (op T)).rightDerived n ⋙
        forget₂ (ModuleCat.{max u v r w} (R.obj.obj (op T)))
          AddCommGrpCat.{max u v r w} ≅
      (representedGamma.{u, v, r, max u v w} R).rightDerived n :=
  Functor.representedRightDerivedPostcompIso _
    (evaluation.{max u v r w} R (op T))
    (forget₂ (ModuleCat.{max u v r w} (R.obj.obj (op T)))
      AddCommGrpCat.{max u v r w}) (representedGammaTerminalIso hT R) n

end SheafOfModules
