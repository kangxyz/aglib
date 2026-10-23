/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ComparisonMap
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.InjectiveAcyclic
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Size

/-!
# Original module Ext and underlying abelian cohomology

Actual injective acyclicity and actual enough injectives supply all-degree
bijectivity of the original comparison. No acyclicity or comparison packet
is assumed. The scalar ring is unchanged.
-/

@[expose] public noncomputable section

universe u v eM eA

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T)
  [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasExt.{eA} (Sheaf J AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v})]

section SmallScalars

variable (R : Sheaf J RingCat.{v})
  [HasExt.{eM} (SheafOfModules.{max u v} R)]

local instance : EnoughInjectives (SheafOfModules.{max u v} R) :=
  SheafOfModules.enoughInjectivesLargeOverSmallScalars.{u, v, 0, v} R

/-- Genuine acyclicity proves bijectivity of the original small-scalar comparison. -/
theorem cohomologyMap_bijective (M : SheafOfModules.{max u v} R) (n : ℕ) :
    Function.Bijective (cohomologyMap hT R M n) :=
  (SheafOfModules.toSheaf R).extPrecompMap_bijective_of_acyclic_injectives
    (liftedUnitIntegerMap hT R) (cohomologyMap_bijective_zero hT R)
    (fun I _ q => toSheaf_injective_cohomology_subsingleton R I hT q) M n

/-- Original module Ext equals original underlying abelian sheaf cohomology. -/
def moduleExtCohomologyAddEquiv (M : SheafOfModules.{max u v} R) (n : ℕ) :
    Ext.{eM} (SheafOfModules.liftedUnit.{u, v, u, v} R) M n ≃+
      Sheaf.H.{eA} ((SheafOfModules.toSheaf R).obj M) n :=
  AddEquiv.ofBijective (cohomologyMap hT R M n) (cohomologyMap_bijective hT R M n)

/-- Its forward map is literally exact scalar forgetting and integer-source precomposition. -/
theorem moduleExtCohomologyAddEquiv_apply (M : SheafOfModules.{max u v} R) (n : ℕ)
    (x : Ext.{eM} (SheafOfModules.liftedUnit.{u, v, u, v} R) M n) :
    moduleExtCohomologyAddEquiv hT R M n x = cohomologyMap hT R M n x := rfl

end SmallScalars

section LargeScalars

variable (R : Sheaf J RingCat.{max u v})
  [HasExt.{eM} (SheafOfModules.{max u v} R)]

local instance : EnoughInjectives (SheafOfModules.{max u v} R) :=
  SheafOfModules.enoughInjectivesLarge.{u, v, 0} R

/-- The same original comparison is bijective for aligned large scalar sheaves. -/
theorem cohomologyMap_bijective_largeScalars (M : SheafOfModules.{max u v} R) (n : ℕ) :
    Function.Bijective (cohomologyMap hT R M n) :=
  (SheafOfModules.toSheaf R).extPrecompMap_bijective_of_acyclic_injectives
    (liftedUnitIntegerMap hT R) (cohomologyMap_bijective_zero hT R)
    (fun I _ q => toSheaf_injective_cohomology_subsingleton_largeScalars R I hT q) M n

/-- Large-valued constant-ring consumers retain the original ring and abelian cohomology. -/
def moduleExtCohomologyAddEquivLargeScalars (M : SheafOfModules.{max u v} R) (n : ℕ) :
    Ext.{eM} (SheafOfModules.liftedUnit.{u, v, max u v, max u v} R) M n ≃+
      Sheaf.H.{eA} ((SheafOfModules.toSheaf R).obj M) n :=
  AddEquiv.ofBijective (cohomologyMap hT R M n)
    (cohomologyMap_bijective_largeScalars hT R M n)

/-- The large-scalar equivalence also has the literal original forward map. -/
theorem moduleExtCohomologyAddEquiv_largeScalars_apply
    (M : SheafOfModules.{max u v} R) (n : ℕ)
    (x : Ext.{eM} (SheafOfModules.liftedUnit.{u, v, max u v, max u v} R) M n) :
    moduleExtCohomologyAddEquivLargeScalars hT R M n x = cohomologyMap hT R M n x := rfl

end LargeScalars

end CategoryTheory.Sheaf.ModuleCoefficients
