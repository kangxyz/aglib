/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Injectives

/-! # Enough injectives after increasing the coefficient universe

This applies the native essentially-small-site construction in any universe
covering the site. It makes no assertion that value lifting preserves injectives.
-/

@[expose] public noncomputable section

universe c h v

namespace CategoryTheory.Sheaf.LargeCohomology

variable {C : Type c} [Category.{h} C]

/-- Native sheafification exists at every value size covering the original site. -/
theorem hasSheafifyRaised (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{max c h v} := by
  let : SmallCategory.{max c h v} (SmallModel.{max c h v, h, c} C) :=
    smallCategorySmallModel.{max c h v, h, c} C
  let : HasSheafify
      ((equivSmallModel.{max c h v, h, c} C).inverse.inducedTopology J)
        AddCommGrpCat.{max c h v} := by
    infer_instance
  exact (equivSmallModel.{max c h v, h, c} C).hasSheafify J
    ((equivSmallModel.{max c h v, h, c} C).inverse.inducedTopology J)
    AddCommGrpCat.{max c h v}

/-- The original sheaf category has enough injectives at every larger value size. -/
theorem enoughInjectivesRaised (J : GrothendieckTopology C) :
    EnoughInjectives (Sheaf J AddCommGrpCat.{max c h v}) := by
  let : SmallCategory.{max c h v} (SmallModel.{max c h v, h, c} C) :=
    smallCategorySmallModel.{max c h v, h, c} C
  let : HasSheafify
      ((equivSmallModel.{max c h v, h, c} C).inverse.inducedTopology J)
        AddCommGrpCat.{max c h v} := by
    infer_instance
  let : HasSheafify J AddCommGrpCat.{max c h v} := hasSheafifyRaised.{c,h,v} J
  let : IsGrothendieckAbelian.{max c h v} (Sheaf J AddCommGrpCat.{max c h v}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max c h v, max c h v, h,
      (max c h v) + 1, c} J AddCommGrpCat.{max c h v}
  infer_instance

end CategoryTheory.Sheaf.LargeCohomology
