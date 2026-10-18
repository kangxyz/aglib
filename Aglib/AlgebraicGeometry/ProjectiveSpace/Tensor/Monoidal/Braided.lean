/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.Functor
public import Aglib.CategoryTheory.Monoidal.Discrete

/-!
# The twisting functor is braided

For the braiding of `Discrete ℤ` by `add_comm` (`Discrete.addBraidedCategory`) and the symmetric
structure of scheme modules, the monoidal twisting functor is braided
(`instBraidedTwistingFunctor`): twist multiplication followed by the transport along
`a + b = b + a` is the braiding of `O(a) ⊗ O(b)` followed by twist multiplication
(`twistingTensorMap_braiding`). The proof evaluates both sides on pure section tensors, using that
the braiding of scheme modules exchanges the two factors (`braiding_hom_moduleTensorSection`, in
`Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections`) and that twist multiplication of
matching chart functions is commutative after transport (`twistingSectionMul_comm`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory BraidedCategory Opposite

namespace AlgebraicGeometry.ProjectiveSpace

open AlgebraicGeometry.Scheme.Modules

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Twist multiplication of sections is commutative, after transport along the commutativity of
degrees. -/
theorem twistingSectionMul_comm (a b : ℤ) (h : a + b = b + a) (U : (ProjectiveSpace R ι).Opens)
    (l : Γ(twistingSheaf R ι a, U)) (m : Γ(twistingSheaf R ι b, U)) :
    (eqToHom (congrArg (twistingSheaf R ι) h)).val.app (op U) (twistingSectionMul R ι a b U l m) =
      twistingSectionMul R ι b a U m l := by
  apply Subtype.ext
  funext i
  refine (twistingSection_eqToHom_val R ι h _ i).trans ?_
  change l.val i * m.val i = m.val i * l.val i
  exact mul_comm _ _

-- The section lemmas of the twists are stated for the `X.ringCatSheaf` spelling of the
-- structure sheaf, which agrees with the module-sheaf spelling only after unfolding; this needs
-- the transparency override, as in the twisting leaves.
set_option backward.isDefEq.respectTransparency false in
/-- Twist multiplication is compatible with the braidings: multiplication followed by the
transport along `a + b = b + a` is the braiding followed by multiplication. -/
theorem twistingTensorMap_braiding (a b : ℤ) (h : a + b = b + a) :
    twistingTensorMap R ι a b ≫ eqToHom (congrArg (twistingSheaf R ι) h) =
      (β_ (twistingSheaf R ι a) (twistingSheaf R ι b)).hom ≫ twistingTensorMap R ι b a := by
  apply moduleTensor_hom_ext
  intro U l m
  -- The right side on a pure tensor; no `eqToHom` occurs here.
  have hR : ((β_ (twistingSheaf R ι a) (twistingSheaf R ι b)).hom ≫
      twistingTensorMap R ι b a).val.app (op U)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a) (twistingSheaf R ι b) U
          l m) =
      twistingSectionMul R ι b a U m l := by
    change (twistingTensorMap R ι b a).val.app (op U)
      ((β_ (twistingSheaf R ι a) (twistingSheaf R ι b)).hom.val.app (op U) _) = _
    rw [braiding_hom_moduleTensorSection, twistingTensorMap_section]
  calc _ = (eqToHom (congrArg (twistingSheaf R ι) h)).val.app (op U)
        ((twistingTensorMap R ι a b).val.app (op U)
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
            (twistingSheaf R ι b) U l m)) := rfl
    _ = (eqToHom (congrArg (twistingSheaf R ι) h)).val.app (op U)
        (twistingSectionMul R ι a b U l m) := by rw [twistingTensorMap_section]
    _ = twistingSectionMul R ι b a U m l := twistingSectionMul_comm R ι a b h U l m
    _ = _ := hR.symm

/-- The twisting functor is braided, for the braiding of `Discrete ℤ` by `add_comm`. -/
instance instBraidedTwistingFunctor : (twistingFunctor R ι).Braided where
  braided m n := twistingTensorMap_braiding R ι m.as n.as (add_comm _ _)

end AlgebraicGeometry.ProjectiveSpace
