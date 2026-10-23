/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.ZModSequence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ConstantRestriction
public import Aglib.CategoryTheory.Sites.SheafCohomology.Vanishing.ExactSequence
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Grp.Zero

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
  (ZMod.mulSequence_shortExact m n hn).map_of_exact (cyclicCoefficientFunctor X)

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- At any fixed degree, vanishing for the cyclic p coefficient implies vanishing for p-powers. -/
theorem cyclicPrimePower_vanishing (p : ℕ) (hp : 0 < p) (q : ℕ)
    [Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod p)) X) q)]
    (r : ℕ) :
    Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r))) X) q) := by
  induction r with
  | zero =>
      change Subsingleton
        (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod 1)) X) q)
      apply Sheaf.subsingleton_H_of_isZero
      exact (cyclicCoefficientFunctor X).map_isZero
        (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (ZMod 1)))
  | succ r ih =>
      let S := (ZMod.mulSequence (p ^ r) p).map (cyclicCoefficientFunctor X)
      let : Subsingleton (Sheaf.H.{w} S.X₁ q) := ih
      let : Subsingleton (Sheaf.H.{w} S.X₃ q) := inferInstanceAs
        (Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod p)) X) q))
      have h := Sheaf.H.subsingleton_middle_of_shortExact
        (cyclicCoefficient_shortExact X (p ^ r) p hp) q
      change Subsingleton
        (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r * p))) X) q) at h
      exact Eq.mpr (congrArg (fun n : ℕ => Subsingleton
        (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X) q))
          (pow_succ p r)) h

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
