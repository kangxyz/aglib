/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryProductSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryWholeMate

/-! # The original ordinary mate is the original product-test square -/
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

/-- The actual ordinary comparison has the original product-square mate. -/
theorem sourceEtaleOrdinaryComparison_mate_product (U : X.Etale) : type_of% (
  (sourceEtaleOrdinaryComparison_mate_whole f f' g g' H U).trans
    (sourceEtaleCompositeDirectIso_eq_product f f' g g' H U)
    ) :=
  (sourceEtaleOrdinaryComparison_mate_whole f f' g g' H U).trans
    (sourceEtaleCompositeDirectIso_eq_product f f' g g' H U)

end AlgebraicGeometry.Scheme.EtaleCohomology
