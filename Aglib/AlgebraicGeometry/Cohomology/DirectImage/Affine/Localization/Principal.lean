/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Localization.Open
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

private abbrev specSectionAlgebra (B : CommRingCat.{u}) (U : (Spec B).Opens) :
    Algebra B Γ(Spec B, U) := inferInstance

private theorem specBasicLocalization (B : CommRingCat.{u}) (r : B) :
    letI := specSectionAlgebra B (PrimeSpectrum.basicOpen r)
    IsLocalization.Away r Γ(Spec B, PrimeSpectrum.basicOpen r) := by
  infer_instance

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
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen r
  let hU : IsAffineOpen U := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) r
  let S := Γ(Spec (CommRingCat.of R), U)
  let : Algebra R S := specSectionAlgebra (CommRingCat.of R) U
  let : IsLocalization.Away r S := specBasicLocalization (CommRingCat.of R) r
  let σ : R →+* S := algebraMap R S
  let V := f ⁻¹ᵁ U
  let q : V.toScheme ⟶ Spec S := (f ∣_ U) ≫ hU.isoSpec.hom
  have h : IsPullback V.ι q f (Spec.map (CommRingCat.ofHom σ)) :=
    Scheme.isPullback_morphismRestrict_isoSpec f U hU
  have hloc : letI := σ.toAlgebra; IsLocalization (Submonoid.powers r) S := by
    have hAlg : σ.toAlgebra = (inferInstance : Algebra R S) :=
      Algebra.algebra_ext _ _ (by intro a; rfl)
    rw [hAlg]
    infer_instance
  exact moduleHPrimeRestriction_isLocalizedModule_of_isPullback
    V q f (Submonoid.powers r) σ h hloc M n

end AlgebraicGeometry.Scheme.Cohomology
