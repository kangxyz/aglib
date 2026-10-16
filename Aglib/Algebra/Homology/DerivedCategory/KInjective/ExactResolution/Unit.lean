/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.ExactResolution
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.InjectiveResolution

/-!
# Exact resolution comparisons and the installed right-derived unit

The actual exact-image augmentation and comparison retain their original
integer complexes in the bounded-below category. A subsequent additive
functor maps the chosen chain comparison through its original installed
derived unit. No exactness of that subsequent functor, nor a
quasi-isomorphism assertion about its image comparison, is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.InjectiveResolution

universe u v u' v' w u'' v'' w'

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B] (F : A ⥤ B) [F.Additive]
  {M : A} (I : InjectiveResolution M)

/-- The original exact-image augmentation, with its actual bounded-below objects. -/
def mapCochainAugmentationPlus :
    (CochainComplex.singleFunctorPlus B 0).obj (F.obj M) ⟶
      F.mapCochainComplexPlus.obj I.cochainComplexPlus :=
  ⟨mapCochainAugmentation F I⟩

variable [HasDerivedCategory.{w} B] [F.PreservesHomology]
  (J : InjectiveResolution (F.obj M))

/-- Native bounded-below localization inverts the actual mapped original augmentation. -/
instance mapCochainAugmentationPlus_isIso_Q :
    IsIso (DerivedCategory.Plus.Q.map (mapCochainAugmentationPlus F I)) :=
  Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso B)
    (mapCochainAugmentationPlus F I)
      (show QuasiIso (mapCochainAugmentation F I) from inferInstance)

/-- The original chosen chain comparison, retaining the original bounded-below complexes. -/
def mapCochainComparisonPlus :
    F.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶ J.cochainComplexPlus :=
  ⟨mapCochainComparison F I J⟩

/-- The bounded-below image is precisely the original augmentation comparison under native Q. -/
theorem mapCochainComparisonPlus_Q_map :
    DerivedCategory.Plus.Q.map (mapCochainComparisonPlus F I J) =
      inv (DerivedCategory.Plus.Q.map (mapCochainAugmentationPlus F I)) ≫
        DerivedCategory.Plus.Q.map J.ιPlus := by
  apply (DerivedCategory.Plus.ι (C := B)).map_injective
  rw [Functor.map_comp, Functor.map_inv]
  change (DerivedCategory.Q (C := B)).map (mapCochainComparison F I J) =
    inv ((DerivedCategory.Q (C := B)).map (mapCochainAugmentation F I)) ≫
      (DerivedCategory.Q (C := B)).map J.ι'
  exact mapCochainComparison_Q_map F I J

variable {D : Type u''} [Category.{v''} D] [Abelian D] [HasDerivedCategory.{w'} D]
  [EnoughInjectives B] (G : B ⥤ D) [G.Additive]

/-- The actual image comparison is the installed right-derived map through its original unit,
with the canonical inverse mapped augmentation. The image map need not be a quasi-isomorphism. -/
theorem mapCochainComparison_rightDerivedUnit :
    DerivedCategory.Plus.Q.map
          (G.mapCochainComplexPlus.map (mapCochainComparisonPlus F I J)) ≫
        (J.rightDerivedFunctorPlusIso G).hom =
      G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
        G.rightDerivedFunctorPlus.map
          (inv (DerivedCategory.Plus.Q.map (mapCochainAugmentationPlus F I))) := by
  have hu := G.rightDerivedFunctorPlusUnit.naturality (mapCochainComparisonPlus F I J)
  change DerivedCategory.Plus.Q.map
        (G.mapCochainComplexPlus.map (mapCochainComparisonPlus F I J)) ≫
      G.rightDerivedFunctorPlusUnit.app J.cochainComplexPlus =
    G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
      G.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (mapCochainComparisonPlus F I J)) at hu
  rw [rightDerivedFunctorPlusIso_hom]
  rw [← Category.assoc, hu]
  rw [mapCochainComparisonPlus_Q_map, Functor.map_comp]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end CategoryTheory.InjectiveResolution
