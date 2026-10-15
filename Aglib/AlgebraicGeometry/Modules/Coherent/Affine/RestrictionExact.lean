/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Support
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Exact
/-!
# Exact principal-open restriction of actual affine coherent sheaves

Geometric restriction is exact, and its kernel is the actual support
subcategory defined by vanishing on the principal open. The categorical
localization universal property belongs to the later localization tier.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

instance affinePrincipalRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (affinePrincipalRestriction R r) := by
  have : PreservesFiniteLimits
      (affinePrincipalRestriction R r ⋙ affineFiniteTypeToModules (CommRingCat.of (Localization.Away
        r))) := by
    rw [affinePrincipalRestriction_comp_inclusion]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (affinePrincipalRestriction R r)
    (affineFiniteTypeToModules (CommRingCat.of (Localization.Away r)))

instance affinePrincipalRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (affinePrincipalRestriction R r) := by
  have : PreservesFiniteColimits
      (affinePrincipalRestriction R r ⋙ affineFiniteTypeToModules (CommRingCat.of (Localization.Away
        r))) := by
    rw [affinePrincipalRestriction_comp_inclusion]
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (affinePrincipalRestriction R r)
    (affineFiniteTypeToModules (CommRingCat.of (Localization.Away r)))

instance affinePrincipalRestriction_additive : (affinePrincipalRestriction R r).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (affinePrincipalRestriction R r)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The exact functor whose underlying functor is actual geometric restriction. -/
def affinePrincipalRestrictionExact :
    ExactFunctor (affineCoherentExactStructure R)
      (affineCoherentExactStructure (CommRingCat.of (Localization.Away r))) where
  toFunctor := affinePrincipalRestriction R r
  map_conflation _ h := h.map_of_exact _

omit [IsNoetherianRing R] in
/-- The kernel is exactly the geometric support subcategory already defined
using actual restriction, equivalently stalk support in the open complement. -/
theorem principalRestriction_kernel_eq_support :
    (affinePrincipalRestriction R r).kernel = affineSupportedAway R (principalOpen R r) := by
  funext M
  apply propext
  change IsZero ((affinePrincipalRestriction R r).obj M) ↔
    IsZero ((affineFiniteTypeToModules (CommRingCat.of (Localization.Away r))).obj
      ((affinePrincipalRestriction R r).obj M))
  exact ⟨Functor.map_isZero _, fun h => IsZero.of_full_of_faithful_of_isZero _ _ h⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
