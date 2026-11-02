/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomologyPullback

/-! # Original integer-to-module-unit source normalization -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wMX wMU wAX wAU

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

example (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] :
    Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1} CategoryTheory.Limits.terminalIsTerminal
        (constantRing X Λ) =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (moduleUnitIntegerScalarHom Λ) ≫ (moduleUnitUnderlyingIso X Λ).hom :=
  liftedUnitIntegerMap_factorization X Λ

example {U X : Scheme.{u}} (f : U ⟶ X) (n : ℕ)
    [HasExt.{wMX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wMU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)]
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    (Sheaf.H.map
        ((moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) f).hom.app M) q).comp
      ((etaleModuleExtCohomologyAddEquivLargeScalars.{u, wMU, wAU} U
          (constantRing U (ULift.{u + 1} (ZMod n)))
          ((moduleInverseImage f (ULift.{u + 1} (ZMod n))).obj M) q).toAddMonoidHom.comp
        (moduleUnitExtPullback.{u, wMX, wMU} f n M q)) =
    (cohomologyPullback.{u, wAX, wAU} f
        ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj M) q).comp
      (etaleModuleExtCohomologyAddEquivLargeScalars.{u, wMX, wAX} X
        (constantRing X (ULift.{u + 1} (ZMod n))) M q).toAddMonoidHom :=
  moduleUnitExtCohomologyPullback_square f n M q

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.liftedUnitIntegerMap_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.liftedUnitIntegerMap_factorization

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.liftedUnitIntegerMap_inverseImage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.liftedUnitIntegerMap_inverseImage

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitExtCohomologyPullback_square' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitExtCohomologyPullback_square
