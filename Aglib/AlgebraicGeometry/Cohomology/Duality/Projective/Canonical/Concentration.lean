/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Detecting native purity concentration on the chart cover

The actual right-derived restriction functors retain native homology.
Consequently their homology bounds on a jointly covering open family give
the same bounds for the installed global derived object. An empty source is
covered by the same argument and requires no dimension inequality.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u v w z
namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type v}
  (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
  (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
  [HasDerivedCategory.{w} X.Modules] [∀ i, HasDerivedCategory.{z} (Y i).Modules]
  (K : DerivedCategory.Plus X.Modules) (c : ℤ)

include hcover

/-- Native lower purity bounds are detected by the actual derived chart restrictions. -/
theorem canonical_isGE_of_derivedRestriction
    (h : ∀ i, ((restrictFunctor (a i)).rightDerivedFunctorPlus.obj K).IsGE c) :
    K.IsGE c := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro k hk
  apply isZero_of_restrict_openCover Y a hcover
  intro i
  let := h i
  exact (DerivedCategory.Plus.isZero_homology_of_isGE
    ((restrictFunctor (a i)).rightDerivedFunctorPlus.obj K) c k hk).of_iso
      (((restrictFunctor (a i)).rightDerivedFunctorPlusHomologyIso k).symm.app K)

/-- Native upper purity bounds are detected by the actual derived chart restrictions. -/
theorem canonical_isLE_of_derivedRestriction
    (h : ∀ i, ((restrictFunctor (a i)).rightDerivedFunctorPlus.obj K).IsLE c) :
    K.IsLE c := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro k hk
  apply isZero_of_restrict_openCover Y a hcover
  intro i
  let := h i
  exact (DerivedCategory.Plus.isZero_homology_of_isLE
    ((restrictFunctor (a i)).rightDerivedFunctorPlus.obj K) c k hk).of_iso
      (((restrictFunctor (a i)).rightDerivedFunctorPlusHomologyIso k).symm.app K)

end AlgebraicGeometry.Scheme.Modules
