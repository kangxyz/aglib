/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.Multiplication
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.Multiply
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence.Sections

/-!
# Twist tensor functors and multiplication through the monoidal structure

The existing comparison `twistingTensorCompIso a b : T_b ⋙ T_a ≅ T_{a+b}` of the twist tensor
functors `T_d = moduleTensorLeftFunctor _ O(d)` is the inverse associator followed by twist
multiplication on the first factor (`twistingTensorCompIso_hom_app`), and the transport of twist
tensor functors along an equality of degrees is the whiskered transport of twists
(`twistingTensorFunctorCongr_hom_app`). The first bridge is checked on nested pure tensors; the
second by `subst`.

With these, multiplication by a global section `s` of `O(a)` on the twist factor,
`moduleTensorCoefficientMap _ (twistingMultiplyGlobal a d s) : T_d ⟶ T_{a+d}`, is compatible
with `twistingTensorCompIso` on the outer factor
(`twistingMultiplyGlobal_coefficientMap_app_tensor_comp`) and on the inner factor
(`twistingMultiplyGlobal_coefficientMap_map_tensor_comp`). Both proofs are associator
naturality and the whiskering laws `twistingMultiplyGlobal_whiskerRight_tensorMap` and
`whiskerLeft_twistingMultiplyGlobal_tensorMap`; no section is evaluated and no transport is
unfolded. That composite is the definition of `twistingTensorMultiply a d s`, so the same
comparisons hold in its spelling (`twistingTensorMultiply_app_tensor_comp`,
`twistingTensorMultiply_map_tensor_comp`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.ProjectiveSpace

open AlgebraicGeometry.Scheme.Modules

variable (R : Type u) [CommRing R] (ι : Type u)

-- The section lemmas of the twists are stated for the `X.ringCatSheaf` spelling of the
-- structure sheaf, which agrees with the module-sheaf spelling only after unfolding; this needs
-- the transparency override, as in the twisting leaves.
set_option backward.isDefEq.respectTransparency false in
/-- The comparison of twist tensor functors is the inverse associator followed by twist
multiplication on the first factor. -/
theorem twistingTensorCompIso_hom_app (a b : ℤ) (F : (ProjectiveSpace R ι).Modules) :
    (twistingTensorCompIso R ι a b).hom.app F =
      (α_ (twistingSheaf R ι a) (twistingSheaf R ι b) F).inv ≫ twistingTensorMap R ι a b ▷ F := by
  apply moduleTensor_nested_hom_ext
  intro U l t n
  -- The source of the component is spelled `(T_b ⋙ T_a).obj F` in the section lemma.
  refine (twistingTensorCompIso_hom_section R ι a b F U l t n).trans ?_
  change _ = (twistingTensorMap R ι a b ▷ F).val.app (op U)
    ((α_ (twistingSheaf R ι a) (twistingSheaf R ι b) F).inv.val.app (op U)
      (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
        (twistingSheaf R ι b ⊗ F) U l
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι b) F U t n)))
  rw [associator_inv_moduleTensorSection]
  -- The first factor is spelled `O(a) ⊗ O(b)` in the section and
  -- `(moduleTensorLeftFunctor _ O(a)).obj O(b)` in the source of `twistingTensorMap`; no
  -- `eqToHom` occurs in this goal.
  erw [whiskerRight_moduleTensorSection]
  rw [twistingTensorMap_section]

/-- The transport of twist tensor functors along an equality of degrees is the whiskered
transport of twists. -/
theorem twistingTensorFunctorCongr_hom_app {c c' : ℤ} (h : c = c')
    (F : (ProjectiveSpace R ι).Modules) :
    (eqToIso (congrArg (fun k ↦ moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι k)) h)).hom.app F =
      eqToHom (congrArg (twistingSheaf R ι) h) ▷ F := by
  subst h
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, eqToHom_refl, id_whiskerRight]
  rfl

-- The source of `twistingTensorMap a b` is spelled `(moduleTensorLeftFunctor _ O(a)).obj O(b)`,
-- the monoidal operations produce `O(a) ⊗ O(b)`; rewriting across the two spellings needs the
-- transparency override.
set_option backward.isDefEq.respectTransparency false in
/-- Multiplying the outer twist factor of `O(d) ⊗ (O(b) ⊗ F)` by a global section `s` of `O(a)`
and merging the twists is merging the twists, multiplying, and transporting along
`a + (d + b) = a + d + b`. -/
theorem twistingMultiplyGlobal_coefficientMap_app_tensor_comp (a d b : ℤ)
    (s : Γ(twistingSheaf R ι a, ⊤)) (F : (ProjectiveSpace R ι).Modules)
    (h : a + (d + b) = a + d + b) :
    (moduleTensorCoefficientMap (ProjectiveSpace R ι) (twistingMultiplyGlobal R ι a d s)).app
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).obj F) ≫
      (twistingTensorCompIso R ι (a + d) b).hom.app F =
    (twistingTensorCompIso R ι d b).hom.app F ≫
      (moduleTensorCoefficientMap (ProjectiveSpace R ι)
        (twistingMultiplyGlobal R ι a (d + b) s)).app F ≫
      (eqToIso (congrArg (fun k ↦ moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι k)) h)).hom.app F := by
  rw [twistingTensorCompIso_hom_app, twistingTensorCompIso_hom_app,
    twistingTensorFunctorCongr_hom_app R ι h]
  change twistingMultiplyGlobal R ι a d s ▷ (twistingSheaf R ι b ⊗ F) ≫
      (α_ (twistingSheaf R ι (a + d)) (twistingSheaf R ι b) F).inv ≫
        twistingTensorMap R ι (a + d) b ▷ F =
    ((α_ (twistingSheaf R ι d) (twistingSheaf R ι b) F).inv ≫ twistingTensorMap R ι d b ▷ F) ≫
      twistingMultiplyGlobal R ι a (d + b) s ▷ F ≫ eqToHom (congrArg (twistingSheaf R ι) h) ▷ F
  rw [associator_inv_naturality_left_assoc,
    ← comp_whiskerRight (twistingMultiplyGlobal R ι a d s ▷ twistingSheaf R ι b)
      (twistingTensorMap R ι (a + d) b) F,
    twistingMultiplyGlobal_whiskerRight_tensorMap R ι a d b s h]
  simp only [comp_whiskerRight, Category.assoc]

-- The source of `twistingTensorMap a b` is spelled `(moduleTensorLeftFunctor _ O(a)).obj O(b)`,
-- the monoidal operations produce `O(a) ⊗ O(b)`; rewriting across the two spellings needs the
-- transparency override.
set_option backward.isDefEq.respectTransparency false in
/-- Multiplying the inner twist factor of `O(e) ⊗ (O(b) ⊗ F)` by a global section `s` of `O(a)`
and merging the twists is merging the twists, multiplying, and transporting along
`a + (e + b) = e + (a + b)`. -/
theorem twistingMultiplyGlobal_coefficientMap_map_tensor_comp (a e b : ℤ)
    (s : Γ(twistingSheaf R ι a, ⊤)) (F : (ProjectiveSpace R ι).Modules)
    (h : a + (e + b) = e + (a + b)) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι e)).map
        ((moduleTensorCoefficientMap (ProjectiveSpace R ι)
          (twistingMultiplyGlobal R ι a b s)).app F) ≫
      (twistingTensorCompIso R ι e (a + b)).hom.app F =
    (twistingTensorCompIso R ι e b).hom.app F ≫
      (moduleTensorCoefficientMap (ProjectiveSpace R ι)
        (twistingMultiplyGlobal R ι a (e + b) s)).app F ≫
      (eqToIso (congrArg (fun k ↦ moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι k)) h)).hom.app F := by
  rw [twistingTensorCompIso_hom_app, twistingTensorCompIso_hom_app,
    twistingTensorFunctorCongr_hom_app R ι h]
  change twistingSheaf R ι e ◁ (twistingMultiplyGlobal R ι a b s ▷ F) ≫
      (α_ (twistingSheaf R ι e) (twistingSheaf R ι (a + b)) F).inv ≫
        twistingTensorMap R ι e (a + b) ▷ F =
    ((α_ (twistingSheaf R ι e) (twistingSheaf R ι b) F).inv ≫ twistingTensorMap R ι e b ▷ F) ≫
      twistingMultiplyGlobal R ι a (e + b) s ▷ F ≫ eqToHom (congrArg (twistingSheaf R ι) h) ▷ F
  rw [associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight (twistingSheaf R ι e ◁ twistingMultiplyGlobal R ι a b s)
      (twistingTensorMap R ι e (a + b)) F,
    whiskerLeft_twistingMultiplyGlobal_tensorMap R ι a e b s h]
  simp only [comp_whiskerRight, Category.assoc]

/-- Multiplying the outer twist factor of `O(d) ⊗ (O(b) ⊗ F)` by a global section `s` of `O(a)`
and merging the twists is merging the twists, multiplying, and transporting along
`a + (d + b) = a + d + b`; stated with `twistingTensorMultiply`. -/
theorem twistingTensorMultiply_app_tensor_comp (a d b : ℤ) (s : Γ(twistingSheaf R ι a, ⊤))
    (F : (ProjectiveSpace R ι).Modules) (h : a + (d + b) = a + d + b) :
    (twistingTensorMultiply R ι a d s).app
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).obj F) ≫
      (twistingTensorCompIso R ι (a + d) b).hom.app F =
    (twistingTensorCompIso R ι d b).hom.app F ≫ (twistingTensorMultiply R ι a (d + b) s).app F ≫
      (eqToIso (congrArg (fun k ↦ moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι k)) h)).hom.app F :=
  twistingMultiplyGlobal_coefficientMap_app_tensor_comp R ι a d b s F h

/-- Multiplying the inner twist factor of `O(e) ⊗ (O(b) ⊗ F)` by a global section `s` of `O(a)`
and merging the twists is merging the twists, multiplying, and transporting along
`a + (e + b) = e + (a + b)`; stated with `twistingTensorMultiply`. -/
theorem twistingTensorMultiply_map_tensor_comp (a e b : ℤ) (s : Γ(twistingSheaf R ι a, ⊤))
    (F : (ProjectiveSpace R ι).Modules) (h : a + (e + b) = e + (a + b)) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι e)).map
        ((twistingTensorMultiply R ι a b s).app F) ≫
      (twistingTensorCompIso R ι e (a + b)).hom.app F =
    (twistingTensorCompIso R ι e b).hom.app F ≫ (twistingTensorMultiply R ι a (e + b) s).app F ≫
      (eqToIso (congrArg (fun k ↦ moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι k)) h)).hom.app F :=
  twistingMultiplyGlobal_coefficientMap_map_tensor_comp R ι a e b s F h

end AlgebraicGeometry.ProjectiveSpace
