/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.RestrictionResolution.RightDerived

/-! # Relative higher-image acyclicity from original represented Ext

Vanishing of the original positive Ext groups from every free representable
makes the original direct-image complex of a supplied injective resolution
exact in positive degrees. The comparison with the native right-derived
functor uses that same resolution. No injectivity after scalar forgetting,
base-change assertion, or properness hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u e

attribute [local instance] hasSheafifyLarge

/-- Original represented Ext vanishing supplies positive acyclicity for the
actual direct image along every scheme morphism, with independent Ext universe. -/
theorem higherDirectImage_isZero_of_representedExt_vanishing
    {X S : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (f : X ⟶ S) (F : AbelianSheaf.{u, u + 1} X)
    (hF : ∀ (U : X.Etale) (n : ℕ),
      Subsingleton (Ext.{e} (freeAbelianSheaf.{u + 1} X.smallEtaleTopology U) F (n + 1)))
    (n : ℕ) : IsZero ((higherDirectImage f (n + 1)).obj F) := by
  exact
    Sheaf.BasisAcyclicity.isZero_rightDerived_pushforward_obj_of_representedExt_vanishing.{
      u + 1, u, u + 1, u, u + 1, e}
      (siteBaseChange f) S.smallEtaleTopology X.smallEtaleTopology F
      (fun W k x => (hF ((siteBaseChange f).obj W) k).elim x 0) n

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
