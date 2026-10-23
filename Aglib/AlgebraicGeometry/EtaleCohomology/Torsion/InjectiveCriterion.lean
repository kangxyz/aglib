/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.CompositeComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Etale

/-!
# Injective coefficient tests for original cohomological pullback

Native module-to-abelian cohomology comparison and the composite Ext criterion
reduce pullback on module coefficients to degree zero and positive vanishing
on the actual pulled-back underlying sheaves of injective module sheaves.
That vanishing remains an explicit application hypothesis. No preservation
of injectivity after scalar forgetting or geometric pullback is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eM eX eS

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]

/-- Actual injective module coefficients suffice for the original pullback comparison. -/
theorem cohomologyPullback_bijective_of_module_injective_acyclic
    (f : S ⟶ X) (R : Sheaf X.smallEtaleTopology RingCat.{u + 1})
    [HasExt.{eM} (SheafOfModules.{u + 1} R)]
    (h₀ : ∀ M : SheafOfModules.{u + 1} R,
      Function.Bijective (cohomologyPullback.{u, eX, eS} f
        ((SheafOfModules.toSheaf R).obj M) 0))
    (hI : ∀ (I : SheafOfModules.{u + 1} R) [Injective I] (n : ℕ),
      Subsingleton (Sheaf.H.{eS}
        ((inverseImage f).obj ((SheafOfModules.toSheaf R).obj I)) (n + 1)))
    (M : SheafOfModules.{u + 1} R) (n : ℕ) :
    Function.Bijective (cohomologyPullback.{u, eX, eS} f
      ((SheafOfModules.toSheaf R).obj M) n) := by
  let : EnoughInjectives (AbelianSheaf.{u, u + 1} X) :=
    abelianSheafEnoughInjectivesLarge X
  let : EnoughInjectives (SheafOfModules.{u + 1} R) :=
    SheafOfModules.enoughInjectivesLarge.{u + 1, u, 0} R
  let a :
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶
      (SheafOfModules.toSheaf R).obj
        (SheafOfModules.liftedUnit.{u + 1, u, u + 1, u + 1} R) :=
    Sheaf.ModuleCoefficients.liftedUnitIntegerMap (etaleTerminalIsTerminal X) R
  exact (SheafOfModules.toSheaf R).extPrecompMap_bijective_on_image_of_acyclic_injectives
    (inverseImage f) a
    (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
    (fun N q => Sheaf.ModuleCoefficients.cohomologyMap_bijective_largeScalars
      (etaleTerminalIsTerminal X) R N q)
    h₀ hI M n

end AlgebraicGeometry.Scheme.EtaleCohomology
