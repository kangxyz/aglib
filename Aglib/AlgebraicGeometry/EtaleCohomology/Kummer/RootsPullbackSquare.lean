/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf

/-! # Original roots cohomology on a commutative square

The four cohomology universes remain independent. This only composes the
existing original roots pullbacks, without selecting a new cohomology model.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u b x y z

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

attribute [local instance] hasSheafifyLarge

/-- The original roots pullbacks commute on an actual scheme square. -/
theorem rootsPullback_commutativeSquare {B X Y Z : Scheme.{u}}
    [hB : HasExt.{b} (AbelianSheaf.{u, u + 1} B)]
    [hX : HasExt.{x} (AbelianSheaf.{u, u + 1} X)]
    [hY : HasExt.{y} (AbelianSheaf.{u, u + 1} Y)]
    [hZ : HasExt.{z} (AbelianSheaf.{u, u + 1} Z)]
    (f : X ⟶ B) (g : Y ⟶ B) (a : Z ⟶ X) (d : Z ⟶ Y)
    (h : a ≫ f = d ≫ g) (n : ℕ) (hn : 0 < n)
    (hi : IsUnit (n : Γ(B, ⊤))) (c : Sheaf.H.{b} (mu B n) 1) :
    rootsCohomologyPullback a n hn (levelInvertible f n hi) 1
      (rootsCohomologyPullback f n hn hi 1 c) =
    rootsCohomologyPullback d n hn (levelInvertible g n hi) 1
      (rootsCohomologyPullback g n hn hi 1 c) := by
  exact (@rootsPullback_comp_unrestricted B X Z hB hX hZ f a n hn hi c).symm.trans
    ((congrArg (fun k : Z ⟶ B =>
      @rootsCohomologyPullback B Z hB hZ k n hn hi 1 c) h).trans
        (@rootsPullback_comp_unrestricted B Y Z hB hY hZ g d n hn hi c))

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
