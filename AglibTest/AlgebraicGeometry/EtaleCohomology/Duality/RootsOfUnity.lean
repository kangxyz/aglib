/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsOfUnity

/-!
# Tests for the sheaf of roots of unity as a sheaf of `ℤ/n`-modules

The example identifies the underlying abelian sheaf of the module sheaf `μ_n` with the
represented sheaf of `n`-th roots of unity, and the axioms are guarded.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry GroupCohomology.Kummer.Coefficients
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

namespace AglibTest.EtaleDualityRootsOfUnity

/-- The underlying abelian sheaf of the module sheaf `μ_n` is `μ_n`. -/
example (X : Scheme.{u}) (n : ℕ) :
    (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj
        (moduleRootsOfUnity X n) ≅ mu X n :=
  moduleRootsOfUnityUnderlyingIso X n

end AglibTest.EtaleDualityRootsOfUnity

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsOfUnity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleRootsOfUnity

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsOfUnityUnderlyingIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleRootsOfUnityUnderlyingIso
