/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleRootsComposition

/-! Public original-map interfaces and approved-axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange

attribute [local instance] hasSheafifyLarge

universe u
variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)

/-- The actual module-root comparison is coherent, including level one. -/
example :
    (moduleInverseImageCompIso (ULift.{u + 1} (ZMod 1)) f g).hom.app
        (moduleRootsOfUnity X 1) ≫
      (moduleInverseImage g (ULift.{u + 1} (ZMod 1))).map
        (moduleRootsOfUnityInverseImageIso f 1 (by decide) (by simp)).hom ≫
      (moduleRootsOfUnityInverseImageIso g 1 (by decide) (by simp)).hom =
        (moduleRootsOfUnityInverseImageIso (g ≫ f) 1 (by decide) (by simp)).hom :=
  moduleRootsOfUnityInverseImageIso_comp f g 1 (by decide) (by simp)

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsOfUnityInverseImageIso_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsOfUnityInverseImageIso_comp

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsOfUnityInverseImageIso_eqToHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsOfUnityInverseImageIso_eqToHom
