/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# Enough injectives for genuine ZMod-valued sheaves

The coefficient ring remains the original `ZMod n`, including `n = 0`.
Native exact filtered colimits and a separator make its module category
Grothendieck in an arbitrary value universe. The native small-model site
construction then supplies sheafification, the Grothendieck property and
enough injectives at the value size covering the original site and hom sets.
No assertion about the underlying abelian sheaf of an injective is made.
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TorsionZMod

/-- The original module forgetful functor preserves filtered colimits even when
its value universe is larger than the unchanged small coefficient ring. -/
theorem moduleForgetPreservesFilteredColimits (n : ℕ) :
    PreservesFilteredColimits (forget (ModuleCat.{w} (ZMod n))) :=
  Limits.comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}) (forget AddCommGrpCat.{w})

/-- The unchanged small coefficient ring has a Grothendieck module category in
any value universe, using native exact filtered colimits and the native separator. -/
theorem moduleIsGrothendieckAbelian (n : ℕ) :
    IsGrothendieckAbelian.{w} (ModuleCat.{w} (ZMod n)) := by
  let : AB5 (ModuleCat.{w} (ZMod n)) := {
    ofShape K _ _ := HasExactColimitsOfShape.domain_of_functor K
      (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}) }
  exact {}

variable {C : Type u} [Category.{v} C]

/-- Genuine ZMod-valued sheaves admit native sheafification at the standard
value size, with the original topology and coefficient ring unchanged. -/
theorem hasSheafifyStandard (J : GrothendieckTopology C) (n : ℕ) :
    HasSheafify J (ModuleCat.{max u v} (ZMod n)) := by
  let : PreservesFilteredColimits (forget (ModuleCat.{max u v} (ZMod n))) :=
    moduleForgetPreservesFilteredColimits n
  let : SmallCategory.{max u v} (SmallModel.{max u v, v, u} C) :=
    smallCategorySmallModel.{max u v, v, u} C
  let : HasSheafify
      ((equivSmallModel.{max u v, v, u} C).inverse.inducedTopology J)
        (ModuleCat.{max u v} (ZMod n)) := by
    infer_instance
  exact (equivSmallModel.{max u v, v, u} C).hasSheafify J
    ((equivSmallModel.{max u v, v, u} C).inverse.inducedTopology J)
      (ModuleCat.{max u v} (ZMod n))

attribute [local instance] hasSheafifyStandard

/-- The actual standard-sized category of genuine ZMod-valued sheaves is
Grothendieck abelian; all small-model and sheafification premises are discharged. -/
theorem isGrothendieckAbelianStandard (J : GrothendieckTopology C) (n : ℕ) :
    IsGrothendieckAbelian.{max u v} (Sheaf J (ModuleCat.{max u v} (ZMod n))) := by
  let : IsGrothendieckAbelian.{max u v} (ModuleCat.{max u v} (ZMod n)) :=
    moduleIsGrothendieckAbelian n
  let : SmallCategory.{max u v} (SmallModel.{max u v, v, u} C) :=
    smallCategorySmallModel.{max u v, v, u} C
  let : HasSheafify
      ((equivSmallModel.{max u v, v, u} C).inverse.inducedTopology J)
        (ModuleCat.{max u v} (ZMod n)) := by
    infer_instance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u v, max u v, v,
    (max u v) + 1, u} J (ModuleCat.{max u v} (ZMod n))

/-- Genuine ZMod-valued sheaves on an arbitrary site have enough injectives
at the standard value size, for every modulus including zero. -/
theorem enoughInjectivesStandard (J : GrothendieckTopology C) (n : ℕ) :
    EnoughInjectives (Sheaf J (ModuleCat.{max u v} (ZMod n))) := by
  let : IsGrothendieckAbelian.{max u v} (Sheaf J (ModuleCat.{max u v} (ZMod n))) :=
    isGrothendieckAbelianStandard J n
  infer_instance

/-- The actual module-sheaf category has Ext in the standard universe, by its
own enough-injectives theorem; no comparison with abelian coefficients is asserted. -/
theorem hasExtStandard (J : GrothendieckTopology C) (n : ℕ) :
    HasExt.{max u v} (Sheaf J (ModuleCat.{max u v} (ZMod n))) := by
  let : EnoughInjectives (Sheaf J (ModuleCat.{max u v} (ZMod n))) :=
    enoughInjectivesStandard J n
  exact hasExt_of_enoughInjectives _

end CategoryTheory.TorsionZMod
