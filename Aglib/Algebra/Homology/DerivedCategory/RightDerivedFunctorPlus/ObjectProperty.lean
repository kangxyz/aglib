/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ShortExact
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.CategoryTheory.Abelian.ObjectProperty.ExactFive
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-! # Weak-Serre properties of original right-derived images

The actual short-exact single triangle and its five-term homology rows prove
extension closure for the original natural-degree right-derived images.
Negative homology vanishes by the native lower bound; no fictitious preceding
natural degree, arbitrary-subobject closure or left exactness is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u' v' w w'

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive]
  (P : ObjectProperty B) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

private theorem property_single_homology_of_rightDerived
    (M : A) (hM : ∀ n : ℕ, P ((F.rightDerived n).obj M)) (i : ℤ) :
    P ((DerivedCategory.Plus.homologyFunctor B i).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M))) := by
  by_cases hi : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact P.prop_of_iso ((F.rightDerivedSingleHomologyIso n).app M) (hM n)
  · exact P.prop_of_isZero (F.isZero_homology_rightDerivedFunctorPlus_of_isGE
      ((DerivedCategory.Plus.singleFunctor A 0).obj M) 0 i (lt_of_not_ge hi))

variable [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]

/-- If the original right-derived images of both ends of a short exact
sequence have a weak-Serre property in every natural degree, the original
middle coefficient has that property in every degree as well. This uses
kernels and cokernels only between known objects, not arbitrary subobjects. -/
theorem rightDerived_property_of_shortExact
    (S : ShortComplex A) (hS : S.ShortExact)
    (h₁ : ∀ n : ℕ, P ((F.rightDerived n).obj S.X₁))
    (h₃ : ∀ n : ℕ, P ((F.rightDerived n).obj S.X₃)) (n : ℕ) :
    P ((F.rightDerived n).obj S.X₂) := by
  let T := DerivedCategory.Plus.ι.mapTriangle.obj
    (F.rightDerivedFunctorPlus.mapTriangle.obj hS.singleTrianglePlus)
  have hT : T ∈ distTriang (DerivedCategory B) :=
    DerivedCategory.Plus.ι.map_distinguished _
      (F.rightDerivedFunctorPlus.map_distinguished _ hS.singleTrianglePlus_distinguished)
  have hleft (i : ℤ) : P ((DerivedCategory.homologyFunctor B i).obj T.obj₁) :=
    property_single_homology_of_rightDerived F P S.X₁ h₁ i
  have hright (i : ℤ) : P ((DerivedCategory.homologyFunctor B i).obj T.obj₃) :=
    property_single_homology_of_rightDerived F P S.X₃ h₃ i
  have hmiddle : P ((DerivedCategory.homologyFunctor B (n : ℤ)).obj T.obj₂) :=
    P.prop_middle_of_exact_five
      (DerivedCategory.HomologySequence.δ T ((n : ℤ) - 1) (n : ℤ) (by omega))
      ((DerivedCategory.homologyFunctor B (n : ℤ)).map T.mor₁)
      ((DerivedCategory.homologyFunctor B (n : ℤ)).map T.mor₂)
      (DerivedCategory.HomologySequence.δ T (n : ℤ) ((n : ℤ) + 1) rfl)
      (DerivedCategory.HomologySequence.exact₁ T hT ((n : ℤ) - 1) (n : ℤ) (by omega))
      (DerivedCategory.HomologySequence.exact₂ T hT (n : ℤ))
      (DerivedCategory.HomologySequence.exact₃ T hT (n : ℤ) ((n : ℤ) + 1) rfl)
      (hright ((n : ℤ) - 1)) (hleft n) (hright n) (hleft ((n : ℤ) + 1))
  exact P.prop_of_iso ((F.rightDerivedSingleHomologyIso n).app S.X₂).symm hmiddle

end CategoryTheory.Functor
