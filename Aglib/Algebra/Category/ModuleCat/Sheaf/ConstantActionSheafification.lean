/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.UnderlyingAction
public import Aglib.Algebra.Category.ModuleCat.ForgetAction
public import Aglib.CategoryTheory.Sites.SheafificationCompositionNaturality

/-! # Noncentral scalar compatibility of the original module sheafification

This is the actual coefficient-comparison square. It uses naturality on the
whole forgetful coefficient functor, not scalar-linearity of ModuleCat.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace ModuleCat.Sheaf
universe u v r
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R]
attribute [local instance] hasSheafify forget_preservesSheafification

/-- Original sheafification comparison intertwines its actual scalar actions. -/
theorem sheafificationUnderlyingIso_scalar
    (P : Cᵒᵖ ⥤ ModuleCat.{max u v} R) (a : R) :
    (sheafComposeNatIso J (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (sheafificationAdjunction J (ModuleCat.{max u v} R))
      (sheafificationAdjunction J AddCommGrpCat.{max u v})).hom.app P ≫
        (underlyingScalar J R a).app ((presheafToSheaf J (ModuleCat.{max u v} R)).obj P) =
    (presheafToSheaf J AddCommGrpCat.{max u v}).map
        (Functor.whiskerLeft P (ModuleCat.forgetScalarAction R a)) ≫
      (sheafComposeNatIso J (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
        (sheafificationAdjunction J (ModuleCat.{max u v} R))
        (sheafificationAdjunction J AddCommGrpCat.{max u v})).hom.app P :=
  sheafComposeNatIso_coefficient_naturality J _ _ (ModuleCat.forgetScalarAction R a) P

end ModuleCat.Sheaf
