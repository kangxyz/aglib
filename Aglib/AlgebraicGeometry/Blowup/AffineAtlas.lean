/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineUniversalProperty

/-!
# Actual saturated atlases for universal affine blowups

The original saturated chart rings, scalar maps and ratio-localization overlaps
give an atlas on the actual Rees Proj. The existing unique comparison transports
that atlas to every universal representative. Actual ideal sheaves on a spectrum
are also identified with their original ring ideals for local constructions.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- The ring ideal of an actual ideal sheaf on a spectrum, transported by the canonical
global-sections isomorphism to the original ring. -/
def spectrumIdeal {A : Type u} [CommRing A] (I : (Spec (.of A)).IdealSheafData) : Ideal A :=
  (I.ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (.of A)).hom.hom

/-- The original quotient centre of the transported ring ideal is the original ideal sheaf. -/
theorem affineCenter_spectrumIdeal {A : Type u} [CommRing A]
    (I : (Spec (.of A)).IdealSheafData) : affineCenter A (spectrumIdeal I) = I := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [affineCenter, Scheme.IdealSheafData.specMap_kernel_top, Ideal.mk_ker,
    spectrumIdeal, Ideal.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).hom)]

/-- The actual native affine Rees Proj realizes the universal datum for any actual ideal
sheaf on a spectrum, with its original structural map. -/
def spectrumDatum {A : Type u} [CommRing A] (I : (Spec (.of A)).IdealSheafData) :
    BlowupDatum I where
  Y := affineProj (spectrumIdeal I)
  map := affineProjMap (spectrumIdeal I)
  cartier := by
    have h := affineProjMap_cartier (spectrumIdeal I)
    rwa [affineCenter_spectrumIdeal I] at h
  universal T f hf := by
    rw [← affineCenter_spectrumIdeal I] at hf
    exact affineProjMap_universal (spectrumIdeal I) T f hf

/-- The literal saturated atlas of the actual affine Rees Proj, including every original
ideal element and the original ratio-localization overlaps. -/
def affineProjAtlas {A : Type u} [CommRing A] (I : Ideal A) :
    AffineAtlas A I (affineProjBlowupDatum I) where
  chart := affineProjChart I
  openImmersion _ := inferInstance
  triangle := affineProjChart_map I
  covers := affineProjChart_covers I
  overlap := affineProjChart_overlap I

/-- The actual saturated atlas on any given universal affine blowup representative,
transported along the unique comparison over the original base. -/
def affineAtlas {A : Type u} [CommRing A] {I : Ideal A}
    (B : BlowupDatum (affineCenter A I)) : AffineAtlas A I B :=
  (affineProjAtlas I).transport B

/-- The exact original affine-atlas family is supplied by the transported actual atlas. -/
theorem blowupAffineAtlas : BlowupAffineAtlas.{u} := by
  intro A _ _ I B
  exact ⟨affineAtlas B⟩

end AlgebraicGeometry.Scheme.Blowup
