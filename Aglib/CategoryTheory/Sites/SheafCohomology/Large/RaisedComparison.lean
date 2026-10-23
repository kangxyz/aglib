/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.RaisedInjectives
public import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Local bijectivity at larger coefficient sizes

The native small-model equivalence transports the existing sheafification
criterion. The original topology and all original coefficient maps are retained.
-/

@[expose] public noncomputable section

universe c h v

namespace CategoryTheory.Sheaf.LargeCohomology

variable {C : Type c} [Category.{h} C]

/-- Local bijectivity characterizes original abelian sheafification at larger values. -/
theorem abWEqualsLocallyBijectiveRaised (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{max c h v} := by
  let : SmallCategory.{max c h v} (SmallModel.{max c h v, h, c} C) :=
    smallCategorySmallModel.{max c h v, h, c} C
  let K := (equivSmallModel.{max c h v, h, c} C).inverse.inducedTopology J
  let : HasSheafify K AddCommGrpCat.{max c h v} := by infer_instance
  let : HasSheafify J AddCommGrpCat.{max c h v} := hasSheafifyRaised.{c, h, v} J
  let : K.WEqualsLocallyBijective AddCommGrpCat.{max c h v} := by infer_instance
  exact GrothendieckTopology.WEqualsLocallyBijective.transport J K
    (equivSmallModel.{max c h v, h, c} C).inverse
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

/-- The native local-bijectivity criterion also transports for larger set values. -/
theorem typeWEqualsLocallyBijectiveRaised (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective (Type (max c h v)) := by
  let : SmallCategory.{max c h v} (SmallModel.{max c h v, h, c} C) :=
    smallCategorySmallModel.{max c h v, h, c} C
  let K := (equivSmallModel.{max c h v, h, c} C).inverse.inducedTopology J
  let : HasSheafify K (Type (max c h v)) := by infer_instance
  let : HasSheafify J (Type (max c h v)) :=
    (equivSmallModel.{max c h v, h, c} C).hasSheafify J K (Type (max c h v))
  let : K.WEqualsLocallyBijective (Type (max c h v)) := by infer_instance
  exact GrothendieckTopology.WEqualsLocallyBijective.transport J K
    (equivSmallModel.{max c h v, h, c} C).inverse
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

end CategoryTheory.Sheaf.LargeCohomology
