/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctor
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.InjectiveResolution

/-! # Actual exact-functor resolution lifts in bounded-below complexes

The native exact-functor lift extends by zero to the actual bounded-below
resolution complexes. Its augmented triangle uses the original inclusion and
single-complex comparison. Injectivity is needed only in the target resolution.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits HomologicalComplex

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.InjectiveResolution.ExactFunctor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {A : C} {B : D} (I : InjectiveResolution A) (J : InjectiveResolution B)
  (a : F.obj A ⟶ B)

/-- The actual native resolution lift, extended by zero with its lower bound retained. -/
def liftPlus : F.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶ J.cochainComplexPlus :=
  ObjectProperty.homMk (extendedLift F I J (lift F I J a))

/-- The actual lift respects the original augmentation, without an extra compatibility premise. -/
theorem liftPlus_augmentation :
    F.mapCochainComplexPlus.map I.ιPlus ≫ liftPlus F I J a =
      (show F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus C 0).obj A) ⟶
          (CochainComplex.singleFunctorPlus D 0).obj (F.obj A) from
        ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).hom.app A)) ≫
        (CochainComplex.singleFunctorPlus D 0).map a ≫ J.ιPlus := by
  apply ObjectProperty.hom_ext
  change (F.mapHomologicalComplex (.up ℤ)).map I.ι' ≫
      extendedLift F I J (lift F I J a) =
    (F.mapCochainComplexSingleFunctor 0).hom.app A ≫
      (CochainComplex.singleFunctor D 0).map a ≫ J.ι'
  apply (cancel_epi ((F.mapCochainComplexSingleFunctor 0).inv.app A)).mp
  rw [Iso.inv_hom_id_app_assoc]
  exact extendedLift_augmentation F I J a (lift F I J a) (lift_commutes_zero F I J a)

end CategoryTheory.InjectiveResolution.ExactFunctor
