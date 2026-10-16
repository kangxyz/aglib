/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Original affine-open spectrum maps and their supplied pullback squares

For an affine open in a spectrum, its original `fromSpec` is the spectrum
map of the original coordinate algebra map. The native affine-open
isomorphism therefore turns actual open restriction of a morphism into
the supplied cartesian square over that same ring map. No replacement
fibre product or chosen geometric isomorphism is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

universe u

namespace IsAffineOpen

variable {R : CommRingCat.{u}} {U : (Spec R).Opens} (hU : IsAffineOpen U)

/-- The original affine-open immersion from its spectrum is the spectrum of the actual
coordinate algebra map. -/
theorem fromSpec_eq_SpecMap_algebraMap :
    hU.fromSpec = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Spec R, U))) := by
  calc
    hU.fromSpec = hU.fromSpec ≫ (Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv := by
      rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    _ = Spec.map ((Spec R).presheaf.map (homOfLE le_top).op) ≫
        Spec.map (Scheme.ΓSpecIso R).inv := by rw [← Category.assoc, hU.fromSpec_toSpecΓ]
    _ = Spec.map ((Scheme.ΓSpecIso R).inv ≫
        (Spec R).presheaf.map (homOfLE le_top).op) := by rw [← Spec.map_comp]
    _ = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Spec R, U))) := rfl

/-- The native affine-open isomorphism retains the original open immersion over the same
coordinate algebra map. -/
theorem isoSpec_hom_SpecMap_algebraMap :
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Spec R, U))) = U.ι := by
  rw [← hU.fromSpec_eq_SpecMap_algebraMap]
  exact hU.isoSpec_hom_fromSpec

end IsAffineOpen

namespace Scheme

/-- Restricting a morphism over a spectrum to an affine target open gives the original
supplied coordinate-ring square under its native affine-open isomorphism. -/
theorem isPullback_morphismRestrict_isoSpec {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (U : (Spec R).Opens) (hU : IsAffineOpen U) :
    IsPullback (f ⁻¹ᵁ U).ι ((f ∣_ U) ≫ hU.isoSpec.hom) f
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(Spec R, U)))) := by
  apply (isPullback_morphismRestrict f U).flip.of_iso
    (Iso.refl _) (Iso.refl _) hU.isoSpec (Iso.refl _)
  · simp
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using
      hU.isoSpec_hom_SpecMap_algebraMap.symm

end Scheme

end AlgebraicGeometry
