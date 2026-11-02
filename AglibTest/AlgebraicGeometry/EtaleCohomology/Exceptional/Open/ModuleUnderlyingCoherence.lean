/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleUnderlyingCoherence

/-! Public original-map interfaces and approved-axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (Λ : Type (u + 1)) [Ring Λ]

/-- The native counit statement needs only a ring and the actual étale morphism. -/
example (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleLowerShriekAdjunction j Λ).counit.app M) =
      (moduleLowerShriekUnderlyingIso j Λ).hom.app ((moduleInverseImage j Λ).obj M) ≫
        (etaleLowerShriek j).map ((moduleInverseImageUnderlyingIso Λ j).hom.app M) ≫
        (etaleLowerShriekAdjunction j).counit.app
          ((SheafOfModules.toSheaf (constantRing X Λ)).obj M) :=
  moduleLowerShriekUnderlyingIso_counit_app j Λ M

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleEtaleSliceUnderlyingIso_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleEtaleSliceUnderlyingIso_inv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.mate_sliceLowerShriekCoefficientIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.mate_sliceLowerShriekCoefficientIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleValuedEtaleRestriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleValuedEtaleRestriction

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleValuedInverseImageUnderlyingIso_etale' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleValuedInverseImageUnderlyingIso_etale

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleValuedLowerShriekRestrictionUnderlyingIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleValuedLowerShriekRestrictionUnderlyingIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleValuedLowerShriekUnderlyingIso_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleValuedLowerShriekUnderlyingIso_inv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleSheafUnderlyingIso_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleSheafUnderlyingIso_inv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleSheafInverseUnderlyingIso_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleSheafInverseUnderlyingIso_inv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleLowerShriekUnderlyingIso_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.mate_moduleLowerShriekUnderlyingIso_inv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekUnderlyingIso_counit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekUnderlyingIso_counit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekUnderlyingIso_counit_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekUnderlyingIso_counit_app

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekUnderlyingIso_unit_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekUnderlyingIso_unit_app
