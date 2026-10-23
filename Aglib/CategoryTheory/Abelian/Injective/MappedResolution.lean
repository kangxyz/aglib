/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Injective.MapAugmentation
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Coefficient-specific mapped injective resolutions

A left exact additive functor preserving injective objects carries an original
resolution to a resolution whenever its mapped complex is exact in positive
degrees. No exactness on other coefficients is required. The augmentation and
maps of resolutions are the original mapped arrows.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v u' v'

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  {M : C} (I : InjectiveResolution M)

/-- Positive exactness and the preserved original kernel suffice for the actual
mapped augmentation to be a quasi-isomorphism. -/
theorem mapAugmentation_quasiIso_of_exactAt
    (hI : ∀ n : ℕ, ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt (n + 1)) :
    QuasiIso (I.mapAugmentation F) := by
  constructor
  intro n
  cases n with
  | zero => exact I.mapAugmentation_quasiIsoAt_zero F
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
    exact hI n

variable [F.PreservesInjectiveObjects]

/-- The literal mapped complex, with its original augmentation, as an injective
resolution under coefficient-specific positive exactness. -/
def mapOfExactAt
    (hI : ∀ n : ℕ, ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt (n + 1)) :
    InjectiveResolution (F.obj M) where
  cocomplex := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  injective n := F.injective_obj_of_injective (I.injective n)
  ι := I.mapAugmentation F
  quasiIso := I.mapAugmentation_quasiIso_of_exactAt F hI

/-- Every original resolution lift maps to the resulting actual resolutions.
This applies to arbitrary coefficient morphisms, not only a chosen linear subcategory. -/
def mapHomOfExactAt
    (hI : ∀ n : ℕ, ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt (n + 1))
    {N : C} {J : InjectiveResolution N}
    (hJ : ∀ n : ℕ, ((F.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).ExactAt (n + 1))
    {f : M ⟶ N} (φ : InjectiveResolution.Hom I J f) :
    InjectiveResolution.Hom (I.mapOfExactAt F hI) (J.mapOfExactAt F hJ) (F.map f) where
  hom := (F.mapHomologicalComplex (.up ℕ)).map φ.hom
  ι_f_zero_comp_hom_f_zero := by
    simpa only [mapOfExactAt, comp_f] using
      congrArg (fun g => g.f 0) (I.mapAugmentation_naturality F φ)

end CategoryTheory.InjectiveResolution
