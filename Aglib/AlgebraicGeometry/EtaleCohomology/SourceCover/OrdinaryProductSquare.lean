/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryNormalizedProduct

/-! # Chain the original normalized product comparison without native rewriting -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (H : IsPullback g' f' f g)

/-- The original composite right square equals the original product square. -/
theorem sourceEtaleCompositeDirectIso_eq_product (U : X.Etale) : type_of% (
  NatTrans.ext (funext (fun F : AbelianSheaf.{u, u + 1} X' =>
    ((congrArg (fun e => e.hom.app F)
      (sourceEtaleCompositeDirectIso_normalization_head f f' g g' H U)).trans
      (sourceEtaleCompositeDirectIso_app_normalized f f' g g' H U F)).trans
      (sourceEtaleNormalizedProduct_app f f' g g' H U F)))
    ) :=
  NatTrans.ext (funext (fun F : AbelianSheaf.{u, u + 1} X' =>
    ((congrArg (fun e => e.hom.app F)
      (sourceEtaleCompositeDirectIso_normalization_head f f' g g' H U)).trans
      (sourceEtaleCompositeDirectIso_app_normalized f f' g g' H U F)).trans
      (sourceEtaleNormalizedProduct_app f f' g g' H U F)))

end AlgebraicGeometry.Scheme.EtaleCohomology
