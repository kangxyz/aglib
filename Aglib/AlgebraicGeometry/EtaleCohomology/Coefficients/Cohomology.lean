/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Comparison
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Ext
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Basic
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Injectives

/-!
# Actual small-etale module and abelian cohomology

The native small-etale category has the required fiber products. The original
abelian-sheaf and module-sheaf existence hypotheses are discharged at the
actual coefficient universe `u+1` and Ext universe `u+2`.
-/

@[expose] public noncomputable section

universe u w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u})

/-- Actual larger-valued abelian sheaves on the small-etale site have enough injectives. -/
theorem abelianSheafEnoughInjectivesLarge :
    EnoughInjectives (AbelianSheaf.{u, u + 1} X) :=
  Sheaf.LargeCohomology.enoughInjectivesLarge.{u + 1, u} (Scheme.smallEtaleTopology X)

local instance : EnoughInjectives (AbelianSheaf.{u, u + 1} X) :=
  abelianSheafEnoughInjectivesLarge X

local instance : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := hasExtStandard X

local instance moduleHasExt (R : Sheaf (Scheme.smallEtaleTopology X) RingCat.{u}) :
    HasExt.{u + 2} (SheafOfModules.{u + 1} R) := SheafOfModules.hasExt R

/-- The original small-scalar etale comparison, with actual size hypotheses discharged. -/
def etaleModuleExtCohomologyAddEquiv
    (R : Sheaf (Scheme.smallEtaleTopology X) RingCat.{u})
    (M : SheafOfModules.{u + 1} R) (n : ℕ) :
    Ext.{u + 2} (SheafOfModules.liftedUnit.{u + 1, u, u + 1, u} R) M n ≃+
      Sheaf.H.{u + 2} ((SheafOfModules.toSheaf R).obj M) n :=
  Sheaf.ModuleCoefficients.moduleExtCohomologyAddEquiv terminalIsTerminal R M n

local instance moduleLargeHasExt
    (R : Sheaf (Scheme.smallEtaleTopology X) RingCat.{u + 1}) :
    HasExt.{u + 2} (SheafOfModules.{u + 1} R) := SheafOfModules.hasExt R

/-- Large-valued constant-ring consumers have the same original etale comparison. -/
def etaleModuleExtCohomologyAddEquivLargeScalars
    (R : Sheaf (Scheme.smallEtaleTopology X) RingCat.{u + 1})
    [HasExt.{w} (SheafOfModules.{u + 1} R)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]
    (M : SheafOfModules.{u + 1} R) (n : ℕ) :
    Ext.{w} (SheafOfModules.liftedUnit.{u + 1, u, u + 1, u + 1} R) M n ≃+
      Sheaf.H.{w'} ((SheafOfModules.toSheaf R).obj M) n :=
  Sheaf.ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars
    terminalIsTerminal R M n

end AlgebraicGeometry.Scheme.EtaleCohomology
