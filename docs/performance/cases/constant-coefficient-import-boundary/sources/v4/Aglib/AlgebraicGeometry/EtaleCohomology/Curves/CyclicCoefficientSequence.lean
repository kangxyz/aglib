/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Coefficient
public import Aglib.CategoryTheory.Sites.SheafCohomology.ConstantCyclic
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# Prime-power constant coefficients via actual cyclic extensions

The two native value lifts and the actual constant-sheaf functor carry the
integer cyclic extension to a short exact sequence. Vanishing then passes
from the prime cyclic coefficient to all its powers, including exponent zero.
This is a vanishing argument, not an invalid extension-surjectivity argument.
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

/-- The actual standard finite-constant coefficient functor, with both native lifts displayed. -/
def cyclicCoefficientFunctor (X : Scheme.{u}) : AddCommGrpCat.{0} ⥤ AbelianSheaf.{u, u + 1} X :=
  AddCommGrpCat.uliftFunctor.{u, 0} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
    constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}

instance (X : Scheme.{u}) : (cyclicCoefficientFunctor X).Additive := by
  unfold cyclicCoefficientFunctor constantSheaf
  infer_instance

instance (X : Scheme.{u}) : PreservesFiniteLimits (cyclicCoefficientFunctor X) := by
  unfold cyclicCoefficientFunctor constantSheaf
  infer_instance

instance (X : Scheme.{u}) : PreservesFiniteColimits (cyclicCoefficientFunctor X) := by
  unfold cyclicCoefficientFunctor constantSheaf
  infer_instance

/-- The original finite-constant cyclic extension is genuinely short exact. -/
theorem cyclicCoefficient_shortExact (X : Scheme.{u}) (m n : ℕ) (hn : 0 < n) :
    ((ZMod.mulSequence m n).map (cyclicCoefficientFunctor X)).ShortExact :=
  Sheaf.cyclicCoefficient_shortExact (cyclicCoefficientFunctor X) m n hn

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- At any fixed degree, vanishing for the cyclic p coefficient implies vanishing for p-powers. -/
theorem cyclicPrimePower_vanishing (p : ℕ) (hp : 0 < p) (q : ℕ)
    [Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod p)) X) q)]
    (r : ℕ) :
    Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r))) X) q) := by
  let : Subsingleton (Sheaf.H.{w}
      ((cyclicCoefficientFunctor X).obj (AddCommGrpCat.of (ZMod p))) q) :=
    inferInstanceAs
      (Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod p)) X) q))
  exact Sheaf.cyclicPrimePower_vanishing (cyclicCoefficientFunctor X) p hp q r

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
