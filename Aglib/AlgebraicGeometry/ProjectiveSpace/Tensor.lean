/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Multiplication
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections

/-!
# Actual tensor multiplication of projective twists

The original bilinear multiplication of matching local twist sections descends through
the native module-sheafification adjunction. Its source is the existing actual sheafified
tensor product, and its value on every original pure-tensor section is the original
section product. In each standard coordinate frame it is ordinary multiplication.
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

/-- The original section product as a map from the native pointwise tensor presheaf. -/
def twistingTensorPresheafMap (a b : ℤ) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := (ProjectiveSpace R ι).presheaf)
        (twistingSheaf R ι a).val (twistingSheaf R ι b).val ⟶
      (twistingSheaf R ι (a + b)).val where
  app V := ModuleCat.ofHom (TensorProduct.lift (twistingSectionMulLinear R ι a b V.unop))
  naturality {V W} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    change twistingSectionMul R ι a b W.unop
        ((twistingSheaf R ι a).val.map f s) ((twistingSheaf R ι b).val.map f t) =
      (twistingSheaf R ι (a + b)).val.map f (twistingSectionMul R ι a b V.unop s t)
    exact (twistingSectionMul_map R ι a b f s t).symm

/-- Actual tensor multiplication `O(a) ⊗ O(b) → O(a+b)`, descended by the original
module-sheafification adjunction from the existing section product. -/
def twistingTensorMap (a b : ℤ) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
        (twistingSheaf R ι b) ⟶ twistingSheaf R ι (a + b) :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := (ProjectiveSpace R ι).ringCatSheaf) (𝟙 _)).homEquiv _ _).symm
      (twistingTensorPresheafMap R ι a b)

/-- The actual tensor map retains the original pure-tensor section and original product. -/
theorem twistingTensorMap_section (a b : ℤ) (V : (ProjectiveSpace R ι).Opens)
    (s : Γ(twistingSheaf R ι a, V)) (t : Γ(twistingSheaf R ι b, V)) :
    (twistingTensorMap R ι a b).val.app (op V)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
          (twistingSheaf R ι b) V s t) = twistingSectionMul R ι a b V s t := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj
    (R := (ProjectiveSpace R ι).presheaf)
    (twistingSheaf R ι a).val (twistingSheaf R ι b).val
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (ProjectiveSpace R ι).ringCatSheaf) (𝟙 _)
  have h : adj.homEquiv P (twistingSheaf R ι (a + b)) (twistingTensorMap R ι a b) =
      twistingTensorPresheafMap R ι a b :=
    (adj.homEquiv _ _).apply_symm_apply _
  exact congrArg (fun φ : P ⟶ (twistingSheaf R ι (a + b)).val =>
    φ.app (op V) (s ⊗ₜ[Γ(ProjectiveSpace R ι, V)] t)) h

/-- In every original coordinate frame, actual tensor multiplication is literal multiplication
of the two original coefficients. -/
theorem twistingTensorMap_local (a b : ℤ) (i : ι)
    (V : (ProjectiveSpace R ι).Opens) (hi : V ≤ coordinateOpen R ι i)
    (s : Γ(twistingSheaf R ι a, V)) (t : Γ(twistingSheaf R ι b, V)) :
    twistingSectionsEquiv R ι (a + b) i hi
        ((twistingTensorMap R ι a b).val.app (op V)
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
            (twistingSheaf R ι b) V s t)) =
      twistingSectionsEquiv R ι a i hi s * twistingSectionsEquiv R ι b i hi t := by
  rw [twistingTensorMap_section, twistingSectionsEquiv_mul]

end AlgebraicGeometry.ProjectiveSpace
