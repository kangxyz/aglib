/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.RightDerived.InjectiveShortComplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts

/-! # Higher vanishing for the original pointwise binary sum

The native split sequence of the original functors computes vanishing of their
pointwise sum through the already constructed right-derived exact sequence.
No replacement derived-functor model or biproduct comparison is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u v u' v'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F G : C ⥤ D) [F.Additive] [G.Additive]

/-- The original pointwise split sequence. -/
abbrev binarySumShortComplex : ShortComplex (C ⥤ D) where
  X₁ := F
  X₂ := (pointwiseBinaryBicone F G).pt
  X₃ := G
  f := (pointwiseBinaryBicone F G).inl
  g := (pointwiseBinaryBicone F G).snd
  zero := by ext X; simp

omit [EnoughInjectives C] in
instance pointwiseBinaryBicone_additive : (pointwiseBinaryBicone F G).pt.Additive where
  map_add := by
    intro X Y a b
    apply biprod.hom_ext <;> simp [pointwiseBinaryBicone, Functor.map_add]

/-- The actual pointwise binary sum is zero in a degree where both original
higher images vanish. -/
theorem rightDerived_pointwiseBinaryBicone_isZero
    {X : C} (I : InjectiveResolution X) (n : ℕ)
    (hF : IsZero ((F.rightDerived n).obj X))
    (hG : IsZero ((G.rightDerived n).obj X)) :
    IsZero (((pointwiseBinaryBicone F G).pt.rightDerived n).obj X) := by
  let S := binarySumShortComplex F G
  have hS (J : C) [Injective J] : (S.map ((evaluation C D).obj J)).ShortExact :=
    (ShortComplex.Splitting.ofHasBinaryBiproduct (F.obj J) (G.obj J)).shortExact
  exact (S.rightDerived_exact₂ I hS n).isZero_X₂
    (hF.eq_of_src _ _) (hG.eq_of_tgt _ _)

end CategoryTheory.Functor
