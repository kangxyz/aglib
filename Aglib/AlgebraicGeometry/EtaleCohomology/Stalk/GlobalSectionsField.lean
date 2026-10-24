/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FieldTerminal
public import Aglib.Algebra.Homology.DerivedCategory.Ext.LinearEquiv

/-! # Original cohomology and higher-image sections over a separably closed field

The existing cohomology-to-higher-sections map is bijective over a separably
closed field in every degree. The proof uses the original presheaf comparison,
its accepted stalk isomorphism, the actual initial pointed terminal object,
and the original represented integer augmentation. There is no Leray premise,
new cohomology model, or claim of edge injectivity over a general base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- Base change of the fixed terminal object makes the original represented
integer augmentation an actual isomorphism. -/
theorem representedIntegerAugmentation_baseChangeTerminal_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) :
    IsIso (representedIntegerAugmentation ((siteBaseChange f).obj (etaleTerminal S))) := by
  let U := (siteBaseChange f).obj (etaleTerminal S)
  have hU : IsTerminal U := (etaleTerminalIsTerminal S).isTerminalObj (siteBaseChange f)
  have : IsIso ((etaleTerminalIsTerminal X).from U) :=
    isIso_of_isTerminal hU (etaleTerminalIsTerminal X) _
  dsimp only [representedIntegerAugmentation]
  infer_instance

/-- The original global-to-terminal represented Ext map is bijective over any
base, because its actual integer-source augmentation is an isomorphism. -/
theorem globalCohomologyTerminalClass_bijective {X S : Scheme.{u}} (f : X ⟶ S)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Function.Bijective (globalCohomologyTerminalClass f F q) := by
  let a := representedIntegerAugmentation ((siteBaseChange f).obj (etaleTerminal S))
  let : IsIso a := representedIntegerAugmentation_baseChangeTerminal_isIso f
  exact (Ext.precompLinearEquiv ℤ (asIso a) F q).bijective

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of Ω)) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance fieldTerminalClassSmall :
    Small.{u + 1} (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q
        ((siteBaseChange f).obj (etaleTerminal (Spec (.of Ω))))) :=
  originalCohomologyPresheaf_small f F q (op (etaleTerminal (Spec (.of Ω))))

/-- The original presheaf comparison is invertible at the actual field terminal
object, by its original stalk isomorphism and the original terminal germs. -/
theorem originalCohomologyToHigherDirectImage_fieldTerminal_isIso :
    IsIso ((originalCohomologyToHigherDirectImage f F q).app
      (op (etaleTerminal (Spec (.of Ω))))) := by
  let Φ := pointSmallEtale (𝟙 (Spec (.of Ω)))
  let α := originalCohomologyToHigherDirectImage f F q
  have h := Φ.toPresheafFiber_naturality α
    (etaleTerminal (Spec (.of Ω))) (fieldTerminalPoint Ω)
  apply (isIso_comp_right_iff _
    (Φ.toPresheafFiber (etaleTerminal (Spec (.of Ω))) (fieldTerminalPoint Ω)
      ((higherDirectImage f q).obj F).obj)).mp
  rw [← h]
  infer_instance

/-- Over a separably closed field, the SAME original cohomology-to-higher-image
section map is bijective in every degree, with the original Ext universe. -/
theorem cohomologyToHigherSections_bijective_of_isSepClosed :
    Function.Bijective (cohomologyToHigherSections f F q) := by
  let := originalCohomologyToHigherDirectImage_fieldTerminal_isIso Ω f F q
  have hα := ConcreteCategory.bijective_of_isIso
    ((originalCohomologyToHigherDirectImage f F q).app
      (op (etaleTerminal (Spec (.of Ω)))))
  have hs : Function.Bijective (fun x : Sheaf.H.{w} F q =>
      Shrink.addEquiv.{u + 1, w}.symm (globalCohomologyTerminalClass f F q x)) :=
    (Shrink.addEquiv.{u + 1, w}.symm.bijective).comp
      (globalCohomologyTerminalClass_bijective f F q)
  have he : (fun x =>
      (originalCohomologyToHigherDirectImage f F q).app
        (op (etaleTerminal (Spec (.of Ω))))
          (Shrink.addEquiv.{u + 1, w}.symm (globalCohomologyTerminalClass f F q x))) =
        cohomologyToHigherSections f F q := by
    funext x
    exact (cohomologyToHigherSections_apply f F q x).symm
  exact he ▸ hα.comp hs

end AlgebraicGeometry.Scheme.EtaleCohomology
