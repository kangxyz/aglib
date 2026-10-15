/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeCategory
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
/-!
# The affine-local coherent-sheaf property

This object property is defined without noetherianity: quasicoherence together
with finite global sections. On a noetherian affine it is exactly the essential
image of the already constructed actual coherent category. Exactness of that
inclusion proves closure under ambient finite limits and finite colimits.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent
variable (R : CommRingCat.{u})

/-- Actual affine quasicoherence and finite generation, with no hidden
noetherianity filter in the predicate. -/
def affineFiniteSheaf : ObjectProperty (Spec R).Modules := fun M =>
  M.IsQuasicoherent ∧ Module.Finite R (moduleSpecΓFunctor.obj M)

instance affineFiniteSheaf_isoClosed : (affineFiniteSheaf R).IsClosedUnderIsomorphisms where
  of_iso e h := by
    have : Module.Finite R (moduleSpecΓFunctor.obj _) := h.2
    exact ⟨(SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e h.1,
      Module.Finite.equiv (moduleSpecΓFunctor.mapIso e).toLinearEquiv⟩

/-- The finite-type quasicoherent property is the essential image of the actual
affine finite-type sheaf category. -/
theorem affineFiniteSheaf_eq_essImage :
    affineFiniteSheaf R = (affineFiniteTypeToModules R).essImage := by
  funext M
  apply propext
  constructor
  · intro h
    exact ⟨⟨⟨M, h.1⟩, h.2⟩, ⟨Iso.refl M⟩⟩
  · rintro ⟨N, ⟨e⟩⟩
    exact (affineFiniteSheaf R).prop_of_iso e ⟨N.obj.property, N.property⟩

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
