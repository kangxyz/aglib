/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekCohomology

/-!
# Tests for the cohomology of an extension by zero computed among modules

The examples take an open immersion `j : U ⟶ X` and `Λ = ULift (ZMod n)`, so that the
right side is `H^r_c(U, F) = Sheaf.H ((etaleLowerShriek j).obj F) r` of Milne, *Lectures on
Étale Cohomology* (v2.21), p. 92, for the underlying sheaf, and guard the axioms of every new
declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

namespace AglibTest.EtaleDualityLowerShriekCohomology

attribute [local instance] hasSheafifyLarge

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)

local instance : HasExt.{u + 2} (ModuleSheaf X (ULift.{u + 1} (ZMod n))) :=
  HasExt.standard _

local instance : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := hasExtStandard X

/-- `Ext^r_{X,n}(ℤ/n, j_! F) ≅ H^r(X, j_! F₀)` on the original objects. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (r : ℕ) :
    Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n))) ((moduleLowerShriek j _).obj F) r ≃+
      Sheaf.H.{u + 2} ((etaleLowerShriek j).obj
        ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj F)) r :=
  moduleLowerShriekCohomologyAddEquiv j _ F r

/-- Naturality in the coefficient sheaf on `U`. -/
example {F F' : ModuleSheaf U (ULift.{u + 1} (ZMod n))} (f : F ⟶ F') (r : ℕ)
    (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n))) ((moduleLowerShriek j _).obj F) r) :
    moduleLowerShriekCohomologyAddEquiv j _ F' r
        (c.comp (Ext.mk₀ ((moduleLowerShriek j _).map f)) (add_zero r)) =
      Sheaf.H.map ((etaleLowerShriek j).map
          ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).map f)) r
        (moduleLowerShriekCohomologyAddEquiv j _ F r c) :=
  moduleLowerShriekCohomologyAddEquiv_naturality j _ f r c

/-- The module connecting map corresponds to the abelian compact-support connecting map. -/
example (S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))) (hS : S.ShortExact) (r : ℕ)
    (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j _).obj S.X₃) r) :
    moduleLowerShriekCohomologyAddEquiv j _ S.X₁ (r + 1)
        (c.comp (shortExact_moduleLowerShriek j _ hS).extClass rfl) =
      Sheaf.H.δ (shortExact_etaleLowerShriek j
          (hS.map_of_exact (SheafOfModules.toSheaf (constantRing U _)))) r (r + 1) rfl
        (moduleLowerShriekCohomologyAddEquiv j _ S.X₃ r c) :=
  moduleLowerShriekCohomologyAddEquiv_connecting j _ S hS r c

end AglibTest.EtaleDualityLowerShriekCohomology

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekCohomologyAddEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekCohomologyAddEquiv

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekCohomologyAddEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekCohomologyAddEquiv_apply

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekCohomologyAddEquiv_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekCohomologyAddEquiv_naturality

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekCohomologyAddEquiv_connecting' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekCohomologyAddEquiv_connecting
