/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductRestriction

/-! # Original unresized fibre-product cohomology diagrams -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u w s e
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- The actual original scheme-H groups and restrictions, before any group resizing. -/
def originalFibreProductCohomologyPresheaf : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{e} where
  obj U := AddCommGrpCat.of
    (Sheaf.H.{e} ((inverseImage (pullback.snd U.unop.hom f)).obj F) q)
  map g := AddCommGrpCat.ofHom (fibreProductCohomologyRestriction f g.unop F q)
  map_id U := by
    apply ConcreteCategory.ext_apply
    intro x
    exact fibreProductCohomologyRestriction_id f F q U.unop x
  map_comp g h := by
    apply ConcreteCategory.ext_apply
    intro x
    exact fibreProductCohomologyRestriction_comp f F q g.unop h.unop x

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
