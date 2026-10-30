/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsComposition

/-! Public original-map interfaces and approved-axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u
variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)

/-- Intrinsic roots composition requires no selected geometric point or Galois category. -/
example (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (inverseImageComp f g).hom.app (mu X n) ≫
      (inverseImage g).map (rootsPullbackIso f n hn hinv).hom ≫
      (rootsPullbackIso g n hn (levelInvertible f n hinv)).hom =
        (rootsPullbackIso (g ≫ f) n hn hinv).hom :=
  rootsPullbackIso_comp f g n hn hinv

/-- info: 'GroupCohomology.Kummer.CoefficientBaseChange.rootsUnit_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GroupCohomology.Kummer.CoefficientBaseChange.rootsUnit_comp

/-- info: 'GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_homEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_homEquiv

/-- info: 'GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_comp

/-- info: 'GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_eqToHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_eqToHom
