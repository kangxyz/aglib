/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Representatives
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Original exact-functor images of supplied injective resolutions

An exact additive functor sends the original resolution augmentation to a
quasi-isomorphism. The native K-injective target representative theorem
then gives an actual chain comparison with any supplied injective resolution
of the image coefficient. Its image under the original localization is
specified exactly, and the original augmentations commute up to an actual
chain homotopy. The image resolution terms need not be injective. The source
needs no derived category and neither category needs enough injectives when
the two actual resolutions are supplied.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.InjectiveResolution

universe u v u' v' w

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B] (F : A ⥤ B) [F.Additive]
  {M : A} (I : InjectiveResolution M)

/-- The actual mapped augmentation retains the original single-complex comparison and original
integer resolution inclusion. It does not assert that the image terms are injective. -/
def mapCochainAugmentation :
    (CochainComplex.singleFunctor B 0).obj (F.obj M) ⟶
      ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) :=
  (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M ≫
    (F.mapHomologicalComplex (.up ℤ)).map I.ι'

/-- Exactness makes the actual mapped original augmentation a quasi-isomorphism. -/
instance mapCochainAugmentation_quasiIso [F.PreservesHomology] :
    QuasiIso (mapCochainAugmentation F I) := by
  unfold mapCochainAugmentation
  infer_instance

/-- The original integer extension of the supplied target resolution is K-injective. -/
local instance resolutionCochainKInjective {N : B} (J : InjectiveResolution N) :
    J.cochainComplex.IsKInjective :=
  CochainComplex.isKInjective_of_injective J.cochainComplex 0

variable [HasDerivedCategory.{w} B] [F.PreservesHomology]
  (J : InjectiveResolution (F.obj M))

/-- An actual chain comparison represents the specified original augmentation comparison under
native localization; exactness does not require preservation of injective objects. -/
def mapCochainComparison :
    ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ⟶ J.cochainComplex :=
  Classical.choose (CochainComplex.exists_chain_representative_of_isKInjective
    (inv ((DerivedCategory.Q (C := B)).map (mapCochainAugmentation F I)) ≫
      (DerivedCategory.Q (C := B)).map J.ι'))

/-- The chain comparison has exactly the original derived arrow determined by the two original
augmentations, including the inverse of the actual mapped source augmentation. -/
theorem mapCochainComparison_Q_map :
    (DerivedCategory.Q (C := B)).map (mapCochainComparison F I J) =
      inv ((DerivedCategory.Q (C := B)).map (mapCochainAugmentation F I)) ≫
        (DerivedCategory.Q (C := B)).map J.ι' :=
  Classical.choose_spec (CochainComplex.exists_chain_representative_of_isKInjective
    (inv ((DerivedCategory.Q (C := B)).map (mapCochainAugmentation F I)) ≫
      (DerivedCategory.Q (C := B)).map J.ι'))

/-- The actual original augmentations commute in the native localization. -/
theorem mapCochainAugmentation_comparison_Q_map :
    (DerivedCategory.Q (C := B)).map
        (mapCochainAugmentation F I ≫ mapCochainComparison F I J) =
      (DerivedCategory.Q (C := B)).map J.ι' := by
  rw [Functor.map_comp, mapCochainComparison_Q_map, IsIso.hom_inv_id_assoc]

/-- The chosen actual comparison is a quasi-isomorphism, because its specified original
localized map is the composite of the two genuine augmentation isomorphisms. -/
theorem mapCochainComparison_quasiIso : QuasiIso (mapCochainComparison F I J) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso B (mapCochainComparison F I J)).mp
  rw [mapCochainComparison_Q_map]
  infer_instance

/-- The original mapped augmentation followed by the actual chain comparison is homotopic to
the original target augmentation, with no injectivity assumption on the mapped source terms. -/
def mapCochainComparison_augmentationHomotopy :
    Homotopy (mapCochainAugmentation F I ≫ mapCochainComparison F I J) J.ι' :=
  CochainComplex.homotopyOfDerivedEqOfIsKInjective _ _
    (mapCochainAugmentation_comparison_Q_map F I J)

end CategoryTheory.InjectiveResolution
