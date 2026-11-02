/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Localization.Open
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Localization.PrincipalGeometry

/-!
# Original principal-open restriction localizes qcqs cohomology

The actual inverse-image open and the original affine-open spectrum
isomorphism supply the canonical localization square. The proved original
open-cohomology restriction theorem therefore applies directly to every
coordinate-ring element and every nonnegative degree.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The unchanged native open-cohomology restriction to the inverse image of a principal
open is the original module-localization map for every quasicoherent coefficient on qcqs `X`. -/
theorem moduleHPrimeRestriction_isLocalizedModule_principal
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (r : R) (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let V := f ⁻¹ᵁ PrimeSpectrum.basicOpen r
    letI := moduleHPrimeModuleOfHom X α M n ⊤
    letI := moduleHPrimeModuleOfHom X α M n V
    IsLocalizedModule.Away r
      (moduleHPrimeRestrictionOfHom X α M n (homOfLE (show V ≤ ⊤ from le_top))) := by
  exact moduleHPrimeRestriction_isLocalizedModule_of_isPullback
    (f ⁻¹ᵁ PrimeSpectrum.basicOpen r) (principalLocalizationProjection f r) f
    (Submonoid.powers r) (principalLocalizationScalar r)
    (principalLocalization_isPullback f r) (principalLocalization_isLocalization r) M n

end AlgebraicGeometry.Scheme.Cohomology
