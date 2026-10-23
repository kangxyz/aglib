/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Enough injectives at the standard large coefficient size

This is the native essentially-small-site Grothendieck construction at the
size covering both site objects and morphisms. The small-model category is
fixed before sheafification is synthesized, avoiding ambiguous universe maxima.
-/

@[expose] public noncomputable section

universe u v

namespace CategoryTheory.Sheaf.LargeCohomology

variable {C : Type u} [Category.{v} C]

/-- Original abelian sheaves with values in the standard larger universe have enough injectives. -/
theorem enoughInjectivesLarge (J : GrothendieckTopology C) :
    EnoughInjectives (Sheaf J AddCommGrpCat.{max u v}) := by
  let : SmallCategory.{max u v} (SmallModel.{max u v, v, u} C) :=
    smallCategorySmallModel.{max u v, v, u} C
  let : HasSheafify
      ((equivSmallModel.{max u v, v, u} C).inverse.inducedTopology J)
        AddCommGrpCat.{max u v} := by
    infer_instance
  let : IsGrothendieckAbelian.{max u v} (Sheaf J AddCommGrpCat.{max u v}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u v, max u v, v,
      (max u v) + 1, u} J AddCommGrpCat.{max u v}
  infer_instance

end CategoryTheory.Sheaf.LargeCohomology
