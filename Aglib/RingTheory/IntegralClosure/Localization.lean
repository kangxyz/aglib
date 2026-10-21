/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization of literal integral closures

The scalar-extension inclusion retains the same ambient elements. Mathlib's
integral-closure localization theorem identifies this original map as the
localization map, and hence as a localized-module map over the base.
-/

@[expose] public section

namespace integralClosure

variable (A D L : Type*) [CommRing A] [CommRing D] [CommRing L]
  [Algebra A D] [Algebra D L] [Algebra A L] [IsScalarTower A D L]

/-- The inclusion of literal integral closures induced by extending the base ring. -/
def scalarExtensionHom : integralClosure A L →ₐ[A] integralClosure D L :=
  Subalgebra.inclusion (show integralClosure A L ≤ (integralClosure D L).restrictScalars A
    from fun _ hx ↦ hx.tower_top)

@[simp]
theorem coe_scalarExtensionHom (x : integralClosure A L) :
    (scalarExtensionHom A D L x : L) = x := rfl

/-- The algebra structure on the literal localized closure uses its original inclusion. -/
abbrev scalarExtensionAlgebra : Algebra (integralClosure A L) (integralClosure D L) :=
  (scalarExtensionHom A D L).toRingHom.toAlgebra

/-- Compatibility of the original base maps with the scalar-extension inclusion. -/
theorem scalarExtension_isScalarTower_base :
    letI := scalarExtensionAlgebra A D L
    IsScalarTower A (integralClosure A L) (integralClosure D L) :=
  IsScalarTower.of_algHom (scalarExtensionHom A D L)

/-- The scalar-extension inclusion leaves the ambient embedding unchanged. -/
theorem scalarExtension_isScalarTower_ambient :
    letI := scalarExtensionAlgebra A D L
    IsScalarTower (integralClosure A L) (integralClosure D L) L := by
  let := scalarExtensionAlgebra A D L
  exact IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

section Localization

variable (M : Submonoid A) [IsLocalization M D]

/-- Localizing the base localizes the literal integral closure along the original
inclusion, without any normality or finiteness hypotheses. -/
theorem scalarExtension_isLocalization :
    letI := scalarExtensionAlgebra A D L
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A L) M)
      (integralClosure D L) := by
  let := scalarExtensionAlgebra A D L
  let := scalarExtension_isScalarTower_base A D L
  let := scalarExtension_isScalarTower_ambient A D L
  let : IsLocalization (Algebra.algebraMapSubmonoid L M) L :=
    IsLocalization.of_le_isUnit (by
      rintro _ ⟨a, ha, rfl⟩
      change IsUnit (algebraMap A L a)
      simpa only [← IsScalarTower.algebraMap_apply A D L] using
        (IsLocalization.map_units D ⟨a, ha⟩).map (algebraMap D L))
  exact IsLocalization.integralClosure M

/-- The actual scalar-extension inclusion is a localized-module map over the base. -/
theorem scalarExtensionHom_isLocalizedModule :
    IsLocalizedModule M (scalarExtensionHom A D L).toLinearMap := by
  let := scalarExtensionAlgebra A D L
  let := scalarExtension_isScalarTower_base A D L
  let := scalarExtension_isScalarTower_ambient A D L
  let := scalarExtension_isLocalization A D L M
  change IsLocalizedModule M
    (IsScalarTower.toAlgHom A (integralClosure A L) (integralClosure D L)).toLinearMap
  infer_instance

end Localization

end integralClosure
