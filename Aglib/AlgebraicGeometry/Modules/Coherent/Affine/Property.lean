/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty

/-!
# Noetherian closure of the affine finite-type property
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

instance affineFiniteSheaf_containsZero : (affineFiniteSheaf R).ContainsZero where
  exists_zero := ⟨(affineFiniteTypeToModules R).obj 0,
    (affineFiniteTypeToModules R).map_isZero (isZero_zero _), by
      rw [affineFiniteSheaf_eq_essImage]
      exact ⟨0, ⟨Iso.refl _⟩⟩⟩

instance affineFiniteSheaf_finiteLimits : (affineFiniteSheaf R).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ := by
    rw [affineFiniteSheaf_eq_essImage]
    infer_instance

instance affineFiniteSheaf_finiteColimits : (affineFiniteSheaf R).IsClosedUnderFiniteColimits where
  isClosedUnderColimitsOfShape J _ _ := by
    rw [affineFiniteSheaf_eq_essImage]
    infer_instance

end AlgebraicGeometry.Scheme.Modules.Coherent
