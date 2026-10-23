/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback

/-!
# Original constant-coefficient restriction for the curve comparison

The all-degree map is the native cohomology pullback followed by the native
constant-coefficient transport. The low-degree proper-henselian results are
kept in the separate LowDegree leaf, not imported by coefficient-only consumers.
-/

@[expose] public noncomputable section

universe u w w'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable (A : Type u) [AddCommGroup A]
  {X S : Scheme.{u}} (f : S ⟶ X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The original all-degree pullback with its canonical constant-coefficient transport. -/
def constantRestriction (q : ℕ) :
    Sheaf.H.{w} (ConstantFinite.coefficient A X) q →+
      Sheaf.H.{w'} (ConstantFinite.coefficient A S) q :=
  (Sheaf.H.map ((inverseImageConstantIso f).app (ConstantFinite.value A)).hom q).comp
    (cohomologyPullback f (ConstantFinite.coefficient A X) q)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
