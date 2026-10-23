/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.UniqueFamily
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.LocalLifting

/-! # The original augmentation of a unique-index cover

The zeroth augmentation factors through the actual free representable of the
covering object and its actual arrow to the base. This retains the source map
needed to turn original classwise cover-effacement into an augmentation lift.
-/

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.Sheaf.Hypercohomology
open CategoryTheory.Sheaf.BasisAcyclicity

namespace CategoryTheory.Presheaf.Cech

universe c h w

variable {C : Type c} [Category.{h} C] (ι : Type w) [Unique ι]
  {U W : C} (g : U ⟶ W) (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max h w}]

/-- The original zero-simplex source projection, followed by the unique-family
identification, on actual free abelian sheaves. -/
def uniqueAugmentationSource :
    (sheafComplex (familyMap (fun _ : ι => Over.mk g)) J).X 0 ⟶
      freeAbelianSheaf.{w} J U :=
  (freeFunctor ⋙ presheafToSheaf J AddCommGrpCat).map
    (tupleSourceZero (familyMap (fun _ : ι => Over.mk g)) ≫ (uniqueFamilyIso ι U).hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The literal zeroth augmentation is the actual represented restriction
preceded by its zero-simplex source projection. -/
theorem sheafAugmentation_zero_uniqueFamily :
    (sheafAugmentation (familyMap (fun _ : ι => Over.mk g)) J).f 0 =
      uniqueAugmentationSource ι g J ≫ (freeAbelianSheafFunctor.{w} J).map g := by
  rw [sheafAugmentation_zero]
  change (freeFunctor ⋙ presheafToSheaf J AddCommGrpCat).map _ =
    (freeFunctor ⋙ presheafToSheaf J AddCommGrpCat).map _ ≫
      (freeFunctor ⋙ presheafToSheaf J AddCommGrpCat).map (uliftYoneda.{w}.map g)
  rw [← Functor.map_comp]
  congr 1
  rw [Category.assoc, uniqueFamilyIso_hom_comp, tupleSourceZero_comp]

end CategoryTheory.Presheaf.Cech
