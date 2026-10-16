/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Multiplication
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.Frames

/-!
# Original frame coefficients of morphisms between twists

Evaluating an actual morphism `O(b) → O(a+b)` on the original standard generator gives
a local function. These functions commute with the original restrictions and satisfy
exactly the original transition law of `O(a)`. No finiteness or base-field premise is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original frame coefficient of a morphism, evaluated at the original source generator. -/
def twistingHomCoefficient (a b : ℤ)
    (f : twistingSheaf R ι b ⟶ twistingSheaf R ι (a + b)) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i) :
    Γ(ProjectiveSpace R ι, V) :=
  twistingSectionsEquiv R ι (a + b) i hi
    (f.val.app (op V) (twistingGenerator R ι b i hi))

/-- Morphism coefficients commute with every original restriction inside a coordinate chart. -/
theorem twistingHomCoefficient_restrict (a b : ℤ)
    (f : twistingSheaf R ι b ⟶ twistingSheaf R ι (a + b)) (i : ι)
    {V W : (ProjectiveSpace R ι).Opens} (h : V ≤ W) (hi : W ≤ coordinateOpen R ι i) :
    sectionRestrict (ProjectiveSpace R ι) h (twistingHomCoefficient R ι a b f i hi) =
      twistingHomCoefficient R ι a b f i (h.trans hi) := by
  unfold twistingHomCoefficient
  rw [← twistingSectionsEquiv_restrict R ι (a + b) i h hi]
  apply congrArg (twistingSectionsEquiv R ι (a + b) i (h.trans hi))
  rw [← PresheafOfModules.naturality_apply f.val, twistingGenerator_restrict R ι b i h hi]

/-- Original morphism coefficients have the exact transition law of the difference twist. -/
theorem twistingHomCoefficient_transition (a b : ℤ)
    (f : twistingSheaf R ι b ⟶ twistingSheaf R ι (a + b)) (i j : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (hj : V ≤ coordinateOpen R ι j) :
    twistingHomCoefficient R ι a b f i hi =
      (coordinateTransitionOn R ι i j hi hj ^ (-a)).val *
        twistingHomCoefficient R ι a b f j hj := by
  let u := coordinateTransitionOn R ι i j hi hj
  have h := twistingSectionsEquiv_transition R ι (a + b) i j hi hj
    (f.val.app (op V) (twistingGenerator R ι b j hj))
  have hleft : twistingSectionsEquiv R ι (a + b) i hi
      (f.val.app (op V) (twistingGenerator R ι b j hj)) =
        (u ^ (-b)).val * twistingHomCoefficient R ι a b f i hi := by
    rw [twistingGenerator_transition R ι b i j hi hj,
      (f.val.app (op V)).hom.map_smul,
      (twistingSectionsEquiv R ι (a + b) i hi).map_smul, smul_eq_mul]
    rfl
  rw [hleft] at h
  change (u ^ (-b)).val * twistingHomCoefficient R ι a b f i hi =
    (u ^ (-(a + b))).val * twistingHomCoefficient R ι a b f j hj at h
  apply (Units.mul_right_inj (u ^ (-b))).mp
  have hu : u ^ (-(a + b)) = u ^ (-b) * u ^ (-a) := by
    rw [← zpow_add]
    congr 1
    omega
  change (u ^ (-b)).val * twistingHomCoefficient R ι a b f i hi =
    (u ^ (-b)).val * ((u ^ (-a)).val * twistingHomCoefficient R ι a b f j hj)
  rw [hu, Units.val_mul, mul_assoc] at h
  exact h

/-- Original frame coefficients preserve addition of actual morphisms. -/
theorem twistingHomCoefficient_add (a b : ℤ)
    (f g : twistingSheaf R ι b ⟶ twistingSheaf R ι (a + b)) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i) :
    twistingHomCoefficient R ι a b (f + g) i hi =
      twistingHomCoefficient R ι a b f i hi + twistingHomCoefficient R ι a b g i hi := by
  change twistingSectionsEquiv R ι (a + b) i hi
    (f.val.app (op V) (twistingGenerator R ι b i hi) +
      g.val.app (op V) (twistingGenerator R ι b i hi)) = _
  exact (twistingSectionsEquiv R ι (a + b) i hi).map_add _ _

/-- For multiplication by a global twist section, the morphism coefficient is exactly its
original restricted frame coefficient. -/
theorem twistingHomCoefficient_multiplyGlobal (a b : ℤ)
    (s : Γ(twistingSheaf R ι a, ⊤)) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i) :
    twistingHomCoefficient R ι a b (twistingMultiplyGlobal R ι a b s) i hi =
      twistingSectionsEquiv R ι a i hi ((twistingSheaf R ι a).val.map (homOfLE le_top).op s) := by
  rw [twistingHomCoefficient, twistingMultiplyGlobal_app, twistingSectionsEquiv_mul,
    twistingSectionsEquiv_generator, mul_one]

end AlgebraicGeometry.ProjectiveSpace
