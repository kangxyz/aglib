/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.DerivedAdjoint
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartAugmentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.MultiplicativeKernelInclusion

/-! # The original derived adjunct at the original terminal chart

The native higher-image section is evaluated by the original fibre-product cohomology unit,
including the existing resize equivalence and represented terminal class.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w s e
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (p : X ⟶ S)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
      ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
    [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]

/-- This is the SAME chart unit on the SAME original terminal represented class. -/
theorem cohomologyToHigherSections_terminalFibreProduct
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{w} F q) :
    cohomologyToHigherSections p F q c =
      (fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p F q).app
        (op (etaleTerminal S))
        ((fibreProductResizeEquiv.{u, w, s, e} p F q (etaleTerminal S)).symm
          (fibreProductCohomologyEquiv.{u, w, s, e} p (etaleTerminal S) F q
            (globalCohomologyTerminalClass p F q c))) := by
  have h := fibreProductCohomologyToHigherDirectImage_apply_resize.{u, w, s, e}
    p (etaleTerminal S) F q
    ((fibreProductResizeEquiv.{u, w, s, e} p F q (etaleTerminal S)).symm
      (fibreProductCohomologyEquiv.{u, w, s, e} p (etaleTerminal S) F q
        (globalCohomologyTerminalClass p F q c)))
  simp only [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply] at h
  exact (cohomologyToHigherSections_apply p F q c).trans h.symm

universe dX dS
variable [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]

/-- Exact H1 value of the original source-shifted adjunct at the original terminal chart unit. -/
theorem cohomologyOriginalDerivedAdjunct_terminalChart_value
    (F : AbelianSheaf.{u, u + 1} X) (c : Sheaf.H.{w} F 1) :
    let U := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    (constantIntegerHomGlobalSectionsIso S).hom.app ((higherDirectImage p 1).obj F)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (AbelianSheaf.{u, u + 1} S) 1).inv.app U ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).map
          (cohomologyOriginalDerivedAdjunct p F c) ≫ (higherDirectImageIso p 1).inv.app F) =
      (fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p F 1).app
        (op (etaleTerminal S))
        ((fibreProductResizeEquiv.{u, w, s, e} p F 1 (etaleTerminal S)).symm
          (fibreProductCohomologyEquiv.{u, w, s, e} p (etaleTerminal S) F 1
            (globalCohomologyTerminalClass p F 1 c))) := by
  exact (cohomologyOriginalDerivedAdjunct_h1_value p F c).trans
    (cohomologyToHigherSections_terminalFibreProduct p F 1 c)

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w s e dX dS
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [hFibreExt : ∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

local instance : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (𝟙 S) f)) :=
  hFibreExt (etaleTerminal S)

/-- The original higher-image section is the actual chart unit on the geometric pullback class. -/
theorem cohomologyToHigherSections_terminalPullback
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{w} F q) :
    cohomologyToHigherSections f F q c =
      (fibreProductCohomologyToHigherDirectImage.{u, w, s, e} f F q).app
        (op (etaleTerminal S))
        ((fibreProductResizeEquiv.{u, w, s, e} f F q (etaleTerminal S)).symm
          (cohomologyPullback.{u, w, e} (pullback.snd (𝟙 S) f) F q c)) := by
  rw [cohomologyToHigherSections_terminalFibreProduct,
    fibreProductCohomologyEquiv_globalTerminalClass]

variable [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]

/-- The exact original source-shifted adjunct evaluates to the actual geometric pullback class. -/
theorem cohomologyOriginalDerivedAdjunct_terminalPullback_value
    (F : AbelianSheaf.{u, u + 1} X) (c : Sheaf.H.{w} F 1) :
    let U := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    (constantIntegerHomGlobalSectionsIso S).hom.app ((higherDirectImage f 1).obj F)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (AbelianSheaf.{u, u + 1} S) 1).inv.app U ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).map
          (cohomologyOriginalDerivedAdjunct f F c) ≫ (higherDirectImageIso f 1).inv.app F) =
      (fibreProductCohomologyToHigherDirectImage.{u, w, s, e} f F 1).app
        (op (etaleTerminal S))
        ((fibreProductResizeEquiv.{u, w, s, e} f F 1 (etaleTerminal S)).symm
          (cohomologyPullback.{u, w, e} (pullback.snd (𝟙 S) f) F 1 c)) := by
  exact (cohomologyOriginalDerivedAdjunct_h1_value f F c).trans
    (cohomologyToHigherSections_terminalPullback f F 1 c)

end AlgebraicGeometry.Scheme.EtaleCohomology
