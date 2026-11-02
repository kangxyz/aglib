/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleUnderlyingComposition

/-! Public original-map interfaces and approved-axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u
variable {V U X : Scheme.{u}} (j : U ⟶ X) (i : V ⟶ U) [Etale j] [Etale i]
  (Λ : Type (u + 1)) [Ring Λ]

/-- Evaluation retains the original module and abelian composition maps for arbitrary rings. -/
example (M : ModuleSheaf V Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleLowerShriekCompIso Λ j i).hom.app M) ≫
      (moduleLowerShriekUnderlyingIso j Λ).hom.app ((moduleLowerShriek i Λ).obj M) ≫
      (etaleLowerShriek j).map ((moduleLowerShriekUnderlyingIso i Λ).hom.app M) =
    (moduleLowerShriekUnderlyingIso (i ≫ j) Λ).hom.app M ≫
      (etaleLowerShriekCompIso j i).hom.app
        ((SheafOfModules.toSheaf (constantRing V Λ)).obj M) :=
  moduleLowerShriekUnderlyingIso_comp_hom_app j i Λ M

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekUnderlyingIso_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekUnderlyingIso_comp

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekUnderlyingIso_comp_hom_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekUnderlyingIso_comp_hom_app
