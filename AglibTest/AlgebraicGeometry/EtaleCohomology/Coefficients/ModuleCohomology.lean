/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomology

/-!
# Tests for the cohomology of constant-ring module sheaves computed among modules

The examples take `Λ = ULift (ZMod n)`, so that the module sheaves are the sheaves of
`ℤ/n`-modules of Milne, *Lectures on Étale Cohomology* (v2.21), p. 102, with the standard Ext
universes, and guard the axioms of every new declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

namespace AglibTest.EtaleDualityModuleCohomology

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) (n : ℕ)

local instance : HasExt.{u + 2} (ModuleSheaf X (ULift.{u + 1} (ZMod n))) :=
  HasExt.standard _

local instance : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := hasExtStandard X

/-- `Ext^q_{X,n}(ℤ/n, G)` is `Sheaf.H` of the underlying abelian sheaf of `G`. -/
example (G : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n))) G q ≃+
      Sheaf.H.{u + 2} ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj G)
        q :=
  etaleModuleExtCohomologyAddEquivLargeScalars X
      (constantRing X (ULift.{u + 1} (ZMod n))) G q

/-- The comparison is natural in `G`. -/
example {G G' : ModuleSheaf X (ULift.{u + 1} (ZMod n))} (f : G ⟶ G') (q : ℕ)
    (x : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n))) G q) :
    etaleModuleExtCohomologyAddEquivLargeScalars X
      (constantRing X (ULift.{u + 1} (ZMod n))) G' q (x.comp (Ext.mk₀ f) (add_zero q)) =
      Sheaf.H.map ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map f) q
        (etaleModuleExtCohomologyAddEquivLargeScalars X
      (constantRing X (ULift.{u + 1} (ZMod n))) G q x) :=
  moduleUnitExtAddEquiv_naturality X _ f q x

/-- The comparison sends the module connecting map to the `Sheaf.H` connecting map. -/
example (S : ShortComplex (ModuleSheaf X (ULift.{u + 1} (ZMod n)))) (hS : S.ShortExact)
    (q : ℕ) (x : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n))) S.X₃ q) :
    etaleModuleExtCohomologyAddEquivLargeScalars X
      (constantRing X (ULift.{u + 1} (ZMod n))) S.X₁ (q + 1) (x.comp hS.extClass rfl) =
      Sheaf.H.δ (hS.map_of_exact (SheafOfModules.toSheaf (constantRing X _))) q (q + 1) rfl
        (etaleModuleExtCohomologyAddEquivLargeScalars X
      (constantRing X (ULift.{u + 1} (ZMod n))) S.X₃ q x) :=
  moduleUnitExtAddEquiv_connecting X _ S hS q x

end AglibTest.EtaleDualityModuleCohomology

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleUnit

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.etaleModuleExtCohomologyAddEquivLargeScalars' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms etaleModuleExtCohomologyAddEquivLargeScalars

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitExtAddEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleUnitExtAddEquiv_apply

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitExtAddEquiv_mk₀' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleUnitExtAddEquiv_mk₀

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitExtAddEquiv_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleUnitExtAddEquiv_naturality

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitExtAddEquiv_connecting' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleUnitExtAddEquiv_connecting
