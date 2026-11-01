/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.Affine

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

/-- The existing structure-sheaf algebra, retained for the original principal chart. -/
abbrev principalSpecSectionAlgebra (B : CommRingCat.{u}) (U : (Spec B).Opens) :
    Algebra B Γ(Spec B, U) := inferInstance

private theorem specBasicLocalization (B : CommRingCat.{u}) (r : B) :
    letI := principalSpecSectionAlgebra B (PrimeSpectrum.basicOpen r)
    IsLocalization.Away r Γ(Spec B, PrimeSpectrum.basicOpen r) := by
  infer_instance

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The original ring map to sections of a principal open. -/
def principalLocalizationScalar (r : R) :
    R →+* Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r) :=
  @algebraMap R _ _ _ (principalSpecSectionAlgebra (CommRingCat.of R) (PrimeSpectrum.basicOpen r))

/-- The actual restricted structural morphism followed by its original affine chart. -/
def principalLocalizationProjection (f : X ⟶ Spec (CommRingCat.of R)) (r : R) :
    (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme ⟶
      Spec (.of Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r)) :=
  (f ∣_ PrimeSpectrum.basicOpen r) ≫
    (IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) r).isoSpec.hom

/-- The literal principal inverse-image open is the supplied localization square. -/
theorem principalLocalization_isPullback (f : X ⟶ Spec (CommRingCat.of R)) (r : R) :
    IsPullback (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι
      (principalLocalizationProjection f r) f
      (Spec.map (CommRingCat.ofHom (principalLocalizationScalar r))) :=
  Scheme.isPullback_morphismRestrict_isoSpec f (PrimeSpectrum.basicOpen r)
    (IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) r)

/-- The scalar structure of the original chart map is precisely principal localization. -/
theorem principalLocalization_isLocalization (r : R) :
    letI := (principalLocalizationScalar r).toAlgebra
    IsLocalization (Submonoid.powers r)
      Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r) := by
  let S := Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r)
  let : Algebra R S := principalSpecSectionAlgebra (CommRingCat.of R) (PrimeSpectrum.basicOpen r)
  have hAlg : (principalLocalizationScalar r).toAlgebra = (inferInstance : Algebra R S) :=
    Algebra.algebra_ext _ _ (by intro a; rfl)
  rw [hAlg]
  exact specBasicLocalization (CommRingCat.of R) r

end AlgebraicGeometry.Scheme.Cohomology
