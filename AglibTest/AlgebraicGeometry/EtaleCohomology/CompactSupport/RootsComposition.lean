/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.RootsComposition

/-! Public original-map interfaces and approved-axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

attribute [local instance] hasSheafifyLarge

universe u w
variable {V U X : Scheme.{u}} (j : U ⟶ X) (i : V ⟶ U)
  [IsOpenImmersion j] [IsOpenImmersion i]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The roots extension square needs no finite-complement or proper-curve premise. -/
example (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ) :
    (CompactSupport.rootsMap (i ≫ j) n hn hinv q).comp
        (CompactSupport.H.map (i ≫ j)
          (rootsPullbackIso i n hn (levelInvertible j n hinv)).hom q) =
      (CompactSupport.rootsMap j n hn hinv q).comp
        (CompactSupport.extensionCohomologyMap i j (mu U n) q) :=
  CompactSupport.rootsMap_extension j i n hn hinv q

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.etaleLowerShriekCompIso_counit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.etaleLowerShriekCompIso_counit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.etaleLowerShriekCompIso_counit_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.etaleLowerShriekCompIso_counit_app

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsExtensionMap_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsExtensionMap_comp

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsExtensionMap_extension' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsExtensionMap_extension

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap_extension' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap_extension
