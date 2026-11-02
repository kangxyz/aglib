/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomology

/-! # The original roots/unit cohomology square, with its geometric level bounds -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wMX wMU wAX wAU

attribute [local instance] hasSheafifyLarge hasSheafifyModules

example {U X : Scheme.{u}} (f : U ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{wMX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wMU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)] (q : ℕ) :
    (moduleRootsUnitExtCohomologyAddEquiv.{u, wMU, wAU} U n q).toAddMonoidHom.comp
        (moduleRootsUnitExtPullback.{u, wMX, wMU} f n hn hinv q) =
      (Kummer.rootsCohomologyPullback.{u, wAX, wAU} f n hn hinv q).comp
        (moduleRootsUnitExtCohomologyAddEquiv.{u, wMX, wAX} X n q).toAddMonoidHom :=
  moduleRootsUnitExtCohomologyPullback_square f n hn hinv q

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsUnitExtCohomologyAddEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsUnitExtCohomologyAddEquiv

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsUnitExtCohomologyPullback_square' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsUnitExtCohomologyPullback_square
