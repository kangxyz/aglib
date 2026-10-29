/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsOfUnityInverseImage

/-!
# Tests for the inverse image of the module sheaf of roots of unity

The examples restate `j^* μ_{n,X} ≅ μ_{n,U}` among sheaves of `ℤ/n`-modules for an open
immersion `j : U ⟶ X` and `0 < n` invertible on `X`, its compatibility with the Kummer
comparison `rootsPullbackIso`, and the fullness of scalar forgetting, and guard the axioms of
every new declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange

universe u

namespace AglibTest.EtaleDualityRootsOfUnityInverseImage

attribute [local instance] hasSheafifyLarge

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) (hn : 0 < n)
  (hinv : IsUnit (n : Γ(X, ⊤)))

/-- The module sheaf `μ_n` restricts to the module sheaf `μ_n`, compatibly with the Kummer
comparison of the underlying sheaves. -/
example :
    (moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity X n) ≅
      moduleRootsOfUnity U n :=
  moduleRootsOfUnityInverseImageIso j n hn hinv

example :
    (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).map
        (moduleRootsOfUnityInverseImageIso j n hn hinv).hom ≫
      (moduleRootsOfUnityUnderlyingIso U n).hom =
    (moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) j).hom.app
        (moduleRootsOfUnity X n) ≫
      (inverseImage j).map (moduleRootsOfUnityUnderlyingIso X n).hom ≫
        (rootsPullbackIso j n hn hinv).hom :=
  moduleRootsOfUnityInverseImageIso_underlying j n hn hinv

/-- Forgetting scalars from sheaves of `ℤ/n`-modules is full. -/
example : (SheafOfModules.toSheaf.{u + 1} (constantRing U (ULift.{u + 1} (ZMod n)))).Full :=
  moduleSheaf_uLiftZMod_toSheaf_full U n

end AglibTest.EtaleDualityRootsOfUnityInverseImage

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleCat_uLiftZMod_forget₂_full' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleCat_uLiftZMod_forget₂_full

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleSheaf_uLiftZMod_toSheaf_full' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleSheaf_uLiftZMod_toSheaf_full

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsOfUnityInverseImageIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsOfUnityInverseImageIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsOfUnityInverseImageIso_underlying' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsOfUnityInverseImageIso_underlying
