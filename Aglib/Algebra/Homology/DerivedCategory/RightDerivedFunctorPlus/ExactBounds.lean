/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure

/-! # Exact original right-derived functors preserve upper bounds -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
universe u v u' v' w w'
variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

/-- Exactness preserves the original homology vanishing above the same bound. -/
theorem rightDerivedFunctorPlus_isLE_of_preservesHomology
    (K : DerivedCategory.Plus A) (b : ℤ) [K.IsLE b] :
    (F.rightDerivedFunctorPlus.obj K).IsLE b := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff]
  apply (DerivedCategory.isLE_iff _ b).mpr
  intro i hi
  change IsZero ((DerivedCategory.Plus.homologyFunctor B i).obj
    (F.rightDerivedFunctorPlus.obj K))
  exact (F.map_isZero (DerivedCategory.Plus.isZero_homology_of_isLE K b i hi)).of_iso
    ((F.rightDerivedFunctorPlusHomologyIso i).app K)

end CategoryTheory.Functor
