/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Identity
/-! # Original derived contraction and its installed composite-unit equation -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace DerivedCategory.Plus
variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory A] (F G : A ⥤ A) [F.Additive] [G.Additive] [G.PreservesHomology]
  (e : F ⋙ G ≅ 𝟭 A)

/-- Derive the actual ordinary contraction, retaining the original two derived functors. -/
def exactDerivedContractionIso :
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ≅ 𝟭 (DerivedCategory.Plus A) :=
  (F.rightDerivedFunctorPlusCompIsoOfPreservesHomology G).symm ≪≫
    (F ⋙ G).rightDerivedFunctorPlusIso e ≪≫ Functor.rightDerivedFunctorPlusIdIso A

/-- The actual contraction retains the original ordinary map and both installed derived units. -/
theorem exactDerivedContractionIso_unit (K : CochainComplex.Plus A) :
    (Functor.rightDerivedFunctorPlusCompUnit F G).app K ≫
        (exactDerivedContractionIso F G e).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus e).hom.app K ≫
          (Functor.mapCochainComplexPlusIdIso A).hom.app K) := by
  have hE := (F ⋙ G).rightDerivedFunctorPlusIso_hom_app e K
  have hC := F.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app G K
  rw [← Functor.rightDerivedFunctorPlusCompUnit_app F G K] at hC
  rw [← hC]
  change (_ ≫ _) ≫ (_ ≫ _ ≫ _) = _
  simp only [Iso.symm_hom, Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc]
  erw [hE]
  rw [Category.assoc, Functor.rightDerivedFunctorPlusIdIso_unit, ← Functor.map_comp]
end DerivedCategory.Plus
