/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesLocalSections
public import Aglib.AlgebraicGeometry.Modules.Rees.AffineCoordinatesRestriction

/-! # Restriction naturality of the actual homogeneous Rees sections -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Rees

open Scheme.Cohomology

variable {A : Type u} [CommRing A] (I : Ideal A)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  (F : X.Modules) [F.IsQuasicoherent]
  {U V : X.Opens}

/-- Restriction of the original ideal-power section module. -/
abbrev powerRestriction (n : ℕ) (hUV : U ≤ V) :
    powerSections I f F n V →ₗ[A] powerSections I f F n U :=
  ((moduleSectionsPresheaf X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    (idealPower X (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      F I n)).map (homOfLE hUV).op).hom

/-- Homogeneous section maps commute with the original restriction maps. -/
theorem homogeneousSectionMap_restriction (n : ℕ)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)
    (m : powerSections I f F n V) :
    coefficientRestriction I f F hUV (homogeneousSectionMap I f F n V hV m) =
      homogeneousSectionMap I f F n U hU (powerRestriction I f F n hUV m) := by
  apply (coefficientSectionsEquiv I f F U hU).injective
  apply Subtype.ext
  rw [coefficientSectionsEquiv_restriction I f F hU hV hUV,
    homogeneousSectionMap_polynomial, homogeneousSectionMap_polynomial,
    PolynomialModule.map_single]
  congr 1
  exact (PresheafOfModules.naturality_apply
    (idealMultipleι X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      F (I ^ n)).val (homOfLE hUV).op m).symm

end AlgebraicGeometry.Scheme.Modules.Rees
