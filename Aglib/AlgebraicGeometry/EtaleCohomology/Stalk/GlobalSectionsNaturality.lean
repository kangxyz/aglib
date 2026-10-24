/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductGermNaturality

/-! # Coefficient naturality of original global higher-image sections

The original represented augmentation and resolution comparison commute with
actual coefficient morphisms. This keeps the coefficient transports in later
original base-change and relative cohomology squares literal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G) (q : ℕ)

/-- Original restriction to the base-changed terminal object commutes with the
original cohomology map on coefficients. -/
theorem globalCohomologyTerminalClass_naturality (x : Sheaf.H.{w} F q) :
    globalCohomologyTerminalClass f G q (Sheaf.H.map a q x) =
      (globalCohomologyTerminalClass f F q x).comp (Ext.mk₀ a) (add_zero q) :=
  (Ext.comp_assoc_of_third_deg_zero
    (Ext.mk₀ (representedIntegerAugmentation ((siteBaseChange f).obj (etaleTerminal S))))
    x (Ext.mk₀ a) (zero_add q)).symm

/-- The SAME original global-cohomology to higher-section map is natural in
coefficients, retaining the original higher direct-image coefficient map. -/
theorem cohomologyToHigherSections_naturality (x : Sheaf.H.{w} F q) :
    (globalSections S).map ((higherDirectImage f q).map a)
        (cohomologyToHigherSections f F q x) =
      cohomologyToHigherSections f G q (Sheaf.H.map a q x) := by
  let y := globalCohomologyTerminalClass f F q x
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app ((resolutionCohomologyToHigherDirectImage f q).naturality a)
      (op (etaleTerminal S)))
    (originalCohomologyResolutionEquiv f (etaleTerminal S) F q y)
  change ((higherDirectImage f q).map a).hom.app (op (etaleTerminal S))
      (((resolutionCohomologyToHigherDirectImage f q).app F).app (op (etaleTerminal S))
        (originalCohomologyResolutionEquiv f (etaleTerminal S) F q y)) =
    ((resolutionCohomologyToHigherDirectImage f q).app G).app (op (etaleTerminal S))
      (originalCohomologyResolutionEquiv f (etaleTerminal S) G q
        (globalCohomologyTerminalClass f G q (Sheaf.H.map a q x)))
  rw [globalCohomologyTerminalClass_naturality,
    originalCohomologyResolutionEquiv_naturality]
  exact h.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
