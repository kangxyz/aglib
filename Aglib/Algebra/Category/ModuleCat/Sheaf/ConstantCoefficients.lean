/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact

/-! # Constant-ring ModuleCat-valued sheaves

These are the native sheaves valued in `ModuleCat R`, not a new category of
module objects. At a value universe containing the site, native sheafification
and composition with scalar forgetting are available. Forgetting commutes with
the original constant-sheaf functor by the native sheafification comparison.
The scalar ring has its independent universe and is not resized.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf

universe u v r w

variable (R : Type r) [Ring R]

/-- Scalar forgetting to types preserves filtered colimits without requiring
the ring and module universes to be equal. -/
theorem forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget (ModuleCat.{w} R)) := by
  let : PreservesColimitsOfSize.{w, w}
      (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{w, r, w, w} R
  exact Limits.comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) (forget AddCommGrpCat.{w})

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Native sheafification for constant-ring modules at the standard site size. -/
theorem hasSheafify : HasSheafify J (ModuleCat.{max u v} R) := by
  let : PreservesFilteredColimits (forget (ModuleCat.{max u v} R)) :=
    forget_preservesFilteredColimits R
  let : SmallCategory.{max u v} (SmallModel.{max u v, v, u} C) :=
    smallCategorySmallModel.{max u v, v, u} C
  let : HasSheafify
      ((equivSmallModel.{max u v, v, u} C).inverse.inducedTopology J)
        (ModuleCat.{max u v} R) := by
    infer_instance
  exact (equivSmallModel.{max u v, v, u} C).hasSheafify J
    ((equivSmallModel.{max u v, v, u} C).inverse.inducedTopology J)
      (ModuleCat.{max u v} R)

attribute [local instance] hasSheafify

/-- The actual underlying abelian sheaf of constant-ring module coefficients. -/
abbrev underlying : Sheaf J (ModuleCat.{max u v} R) ⥤
    Sheaf J AddCommGrpCat.{max u v} :=
  sheafCompose J (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})

/-- Scalar forgetting preserves the native sheafification equivalences. -/
theorem forget_preservesSheafification :
    J.PreservesSheafification
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) := by
  let : PreservesFilteredColimits (forget (ModuleCat.{max u v} R)) :=
    forget_preservesFilteredColimits R
  let : PreservesColimitsOfSize.{max u v, max u v}
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max u v, r, max u v, max u v} R
  let : PreservesLimitsOfSize.{max u v, max u v}
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) :=
    ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{max u v, max u v, max u v, r}
  exact GrothendieckTopology.instPreservesSheafification J
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})

attribute [local instance] forget_preservesSheafification

/-- Forgetting the actual constant module sheaf gives the actual constant
abelian sheaf, with the native constant-sheaf comparison. -/
def constantUnderlyingIso :
    constantSheaf J (ModuleCat.{max u v} R) ⋙ underlying R J ≅
      forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v} ⋙
        constantSheaf J AddCommGrpCat.{max u v} :=
  constantCommuteCompose J
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})

end ModuleCat.Sheaf
