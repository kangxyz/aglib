/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.Cohomology
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedComparison
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!
# Actual constant-coefficient derived etale sections

The source derives native module-valued terminal sections with the original
constant coefficient action. All existence hypotheses are discharged for the
original small-etale site, module values in universe `u+1`, and Ext in `u+2`.
No invertibility condition is imposed on the coefficient ring.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open CategoryTheory.Sheaf.ModuleCoefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable (X : Scheme.{u})

attribute [local instance] hasSheafifyLarge

local instance : EnoughInjectives (AbelianSheaf.{u, u + 1} X) :=
  abelianSheafEnoughInjectivesLarge X

local instance : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := hasExtStandard X

local instance derivedModuleHasExt (R : Sheaf (Scheme.smallEtaleTopology X) RingCat.{u}) :
    HasExt.{u + 2} (SheafOfModules.{u + 1} R) := SheafOfModules.hasExt R

local instance moduleEnoughInjectives
    (R : Sheaf (Scheme.smallEtaleTopology X) RingCat.{u}) :
    EnoughInjectives (SheafOfModules.{u + 1} R) :=
  SheafOfModules.enoughInjectivesLargeOverSmallScalars.{u + 1, u, 0, u} R

/-- Constant coefficients on the original small-etale site, without invertibility hypotheses. -/
def etaleConstantDerivedCohomologyAddEquiv (Λ : RingCat.{u})
    (M : SheafOfModules.{u + 1}
      ((constantSheaf (Scheme.smallEtaleTopology X) RingCat).obj Λ)) (n : ℕ) :
    ((constantTerminalSections.{u + 1, u, u, 0} (J := Scheme.smallEtaleTopology X)
      terminalIsTerminal Λ).rightDerived n).obj M ≃+
      Sheaf.H.{u + 2} ((SheafOfModules.toSheaf _).obj M) n :=
  constantDerivedCohomologyAddEquiv.{u + 1, u, u + 2, u + 2}
    terminalIsTerminal Λ M n

end AlgebraicGeometry.Scheme.EtaleCohomology
