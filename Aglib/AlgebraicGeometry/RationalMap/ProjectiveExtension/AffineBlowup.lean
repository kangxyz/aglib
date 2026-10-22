/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension.AffineCoordinates
public import Aglib.RingTheory.Localization.ProjectiveCoordinates

/-!
# Native blowups of affine homogeneous coordinate ideals

The original affine coordinates supply the epimorphic row, rather than
assuming it. Common denominators on a principal localization give a coordinate
ideal whose native blowup is unchanged after that localization.

The projective map has its actual base triangle. Identification of its
restriction with the original affine-space map is not asserted here: that
requires the separate line-source naturality comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.RationalCoordinates

variable (A : Type u) [CommRing A] {I : Type u} [Finite I] (v : I → A)

theorem affineUnit_locallyRankOne :
    IsLocallyRankOne (Spec (.of A)) (SheafOfModules.unit (Spec (.of A)).ringCatSheaf) := by
  rw [isLocallyRankOne_iff_local_unit]
  intro x
  exact ⟨⊤, trivial, ⟨Iso.refl _⟩⟩

variable {R : Type u} [CommRing R] (p : Spec (.of A) ⟶ Spec (.of R))

/-- The projective map of the original ring coordinate family, on its actual
native coordinate-ideal blowup. No row or line-module existence is assumed. -/
def affineCoordinateBlowupMap :
    (Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).Y ⟶
      ProjectiveSpace R I := by
  letI : Epi (Sigma.desc (affineCoordinate A v)) := affineCoordinate_epi A v
  exact lineSourceBlowupMap _ _ (affineCoordinate A v) (affineUnit_locallyRankOne A) p

/-- The affine construction retains the original structural morphism. -/
@[reassoc]
theorem affineCoordinateBlowupMap_toSpec :
    affineCoordinateBlowupMap A v p ≫ ProjectiveSpace.toSpec R I =
      (Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).map ≫ p := by
  let : Epi (Sigma.desc (affineCoordinate A v)) := affineCoordinate_epi A v
  exact lineSourceBlowupMap_toSpec _ _ _ _ _

omit [Finite I] in
/-- A coordinate-ideal blowup over a Noetherian affine source is proper. -/
theorem affineCoordinateBlowup_isProper [IsNoetherianRing A] :
    IsProper (Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).map :=
  (Blowup.blowupDatum _).isProper_of_isLocallyNoetherian

/-- The native quotient centre of the unit ring ideal is the unit ideal sheaf. -/
private theorem affineCenter_top (S : Type u) [CommRing S] :
    Blowup.affineCenter S ⊤ = ⊤ := by
  have h : Blowup.spectrumIdeal (⊤ : (Spec (.of S)).IdealSheafData) = ⊤ := by
    simp [Blowup.spectrumIdeal, Ideal.map_top]
  rw [← h]
  exact Blowup.affineCenter_spectrumIdeal _

/-- The complete principal localization, not just its generic point, avoids
the actual homogeneous-coordinate centre. -/
theorem principalCoordinateCenter_comap_eq_top {ι : Type u}
    (f : A) (n : ℕ) (a : ι → A) :
    (Blowup.affineCenter A (IsLocalization.Away.principalCoordinateIdeal f n a)).comap
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) = ⊤ := by
  rw [Blowup.BaseChange.affineCenter_comap,
    IsLocalization.Away.principalCoordinateIdeal_map_eq_top, affineCenter_top]

/-- The literal pullback projection of the native coordinate blowup is an
isomorphism over the entire principal localization. -/
theorem principalCoordinateBlowup_isIso {ι : Type u}
    (f : A) (n : ℕ) (a : ι → A) :
    IsIso (pullback.snd
      (Blowup.blowupDatum (Blowup.affineCenter A
        (IsLocalization.Away.principalCoordinateIdeal f n a))).map
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))) :=
  (Blowup.blowupDatum _).pullback_snd_isIso_of_comap_eq_top _
    (principalCoordinateCenter_comap_eq_top A f n a)

end AlgebraicGeometry.Scheme.RationalCoordinates
