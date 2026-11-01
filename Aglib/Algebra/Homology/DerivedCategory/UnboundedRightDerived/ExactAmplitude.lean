/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Exact native derived functors preserve upper bounds -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w u' v' w'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The original localization of an exact functor preserves native upper
cohomological bounds, with no bounded-below hypothesis. -/
theorem mapDerivedCategory_isLE (X : DerivedCategory C) (n : ℤ) [X.IsLE n] :
    (F.mapDerivedCategory.obj X).IsLE n := by
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE n
  let : K.IsStrictlyLE n := hK
  let eF : F.mapDerivedCategory.obj X ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K
  exact DerivedCategory.TStructure.t.isLE_of_iso eF.symm n

end CategoryTheory.Functor
