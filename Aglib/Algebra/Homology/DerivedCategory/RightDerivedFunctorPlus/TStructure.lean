/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Lower cohomological bounds for the installed right-derived functor

An additive functor's native bounded-below right-derived functor preserves
every lower cohomological bound. The proof uses the native injective
representative in that same lower range and the original derived unit.
Neither left exactness nor homology preservation is required. These bounds
are shared by truncation arguments for base change and coherent images.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u v u' v'

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
    [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]

/-- The original right-derived functor preserves every lower cohomological bound,
even when the original additive functor is not left exact. -/
theorem rightDerivedFunctorPlus_isGE (K : DerivedCategory.Plus A) (n : ℤ)
    [K.IsGE n] : (F.rightDerivedFunctorPlus.obj K).IsGE n := by
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let : I.obj.IsStrictlyGE n := hI
  let J := (InjectiveObject.ι A).mapCochainComplexPlus.obj I
  let : J.obj.IsStrictlyGE n := by
    change CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι A).mapHomologicalComplex (.up ℤ)).obj I.obj) n
    exact (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      (K := I.obj) (InjectiveObject.ι A) n).mpr hI
  let : (F.mapCochainComplexPlus.obj J).obj.IsStrictlyGE n := by
    change CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (.up ℤ)).obj J.obj) n
    infer_instance
  let : (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj J)).IsGE n := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    change (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj J.obj)).IsGE n
    infer_instance
  let e' : DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj J) ≅
      F.rightDerivedFunctorPlus.obj K :=
    asIso (F.rightDerivedFunctorPlusUnit.app J) ≪≫ F.rightDerivedFunctorPlus.mapIso e
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso e' n

/-- Native homology below a lower bound remains zero after the installed right derivation. -/
theorem isZero_homology_rightDerivedFunctorPlus_of_isGE
    (K : DerivedCategory.Plus A) (n i : ℤ) [K.IsGE n] (hi : i < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor B i).obj
      (F.rightDerivedFunctorPlus.obj K)) := by
  let := F.rightDerivedFunctorPlus_isGE K n
  exact DerivedCategory.Plus.isZero_homology_of_isGE _ n i hi

end CategoryTheory.Functor
