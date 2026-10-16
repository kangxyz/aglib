/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.Frames

/-!
# Original tensor generators of projective twists

The pure tensors of the original standard generators have the product transition law.
Actual tensor multiplication sends them to the original generator of the sum twist.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Original pure tensor sections multiply the two original section-ring scalars. -/
theorem twistingTensorSection_smul_smul (a b : ℤ) (V : (ProjectiveSpace R ι).Opens)
    (r t : Γ(ProjectiveSpace R ι, V))
    (s : Γ(twistingSheaf R ι a, V)) (v : Γ(twistingSheaf R ι b, V)) :
    moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
        (twistingSheaf R ι b) V (r • s) (t • v) =
      (r * t) • moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
        (twistingSheaf R ι b) V s v := by
  let η : (Γ(twistingSheaf R ι a, V) ⊗[Γ(ProjectiveSpace R ι, V)]
      Γ(twistingSheaf R ι b, V)) →ₗ[Γ(ProjectiveSpace R ι, V)]
      Γ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
        (twistingSheaf R ι b), V) :=
    (((SheafOfModulesOfCommRing.associatedSheafUnit (ProjectiveSpace R ι).sheaf).app
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj
        (R := (ProjectiveSpace R ι).presheaf)
        (twistingSheaf R ι a).val (twistingSheaf R ι b).val)).app (op V)).hom
  change η ((r • s) ⊗ₜ[Γ(ProjectiveSpace R ι, V)] (t • v)) =
    (r * t) • η (s ⊗ₜ[Γ(ProjectiveSpace R ι, V)] v)
  rw [TensorProduct.smul_tmul_smul, η.map_smul]

/-- The pure tensor of the original standard generators on a coordinate subopen. -/
def twistingTensorGenerator (a b : ℤ) (i : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) :
    Γ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
      (twistingSheaf R ι b), V) :=
  moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a) (twistingSheaf R ι b) V
    (twistingGenerator R ι a i hi) (twistingGenerator R ι b i hi)

/-- Tensor generators retain the original section restriction maps. -/
theorem twistingTensorGenerator_restrict (a b : ℤ) (i : ι)
    {V W : (ProjectiveSpace R ι).Opens} (h : V ≤ W) (hi : W ≤ coordinateOpen R ι i) :
    ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
        (twistingSheaf R ι b)).val.map (homOfLE h).op
        (twistingTensorGenerator R ι a b i hi) =
      twistingTensorGenerator R ι a b i (h.trans hi) := by
  change _ = moduleTensorSection (ProjectiveSpace R ι) _ _ _ _ _
  change ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
    (twistingSheaf R ι b)).presheaf.map (homOfLE h).op _ = _
  rw [twistingTensorGenerator, moduleTensorSection_restrict]
  change moduleTensorSection (ProjectiveSpace R ι) _ _ V
    ((twistingSheaf R ι a).val.map (homOfLE h).op (twistingGenerator R ι a i hi))
    ((twistingSheaf R ι b).val.map (homOfLE h).op (twistingGenerator R ι b i hi)) = _
  rw [twistingGenerator_restrict R ι a i h hi, twistingGenerator_restrict R ι b i h hi]

/-- The original tensor generators have exactly the transition law of the sum twist. -/
theorem twistingTensorGenerator_transition (a b : ℤ) (i j : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (hj : V ≤ coordinateOpen R ι j) :
    twistingTensorGenerator R ι a b j hj =
      (coordinateTransitionOn R ι i j hi hj ^ (-(a + b))).val •
        twistingTensorGenerator R ι a b i hi := by
  unfold twistingTensorGenerator
  rw [twistingGenerator_transition R ι a i j hi hj,
    twistingGenerator_transition R ι b i j hi hj, twistingTensorSection_smul_smul]
  simp only [neg_add, zpow_add, Units.val_mul]

/-- Actual multiplication sends the tensor of the original generators to the original
sum-twist generator, with coefficient exactly one. -/
theorem twistingTensorMap_generator (a b : ℤ) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i) :
    (twistingTensorMap R ι a b).val.app (op V) (twistingTensorGenerator R ι a b i hi) =
      twistingGenerator R ι (a + b) i hi := by
  apply (twistingSectionsEquiv R ι (a + b) i hi).injective
  rw [twistingTensorGenerator, twistingTensorMap_local,
    twistingSectionsEquiv_generator, twistingSectionsEquiv_generator,
    twistingSectionsEquiv_generator, mul_one]

end AlgebraicGeometry.ProjectiveSpace
