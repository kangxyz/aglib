/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Flat base change of the original schematic image

The original image factor is schematically dominant. Flat base change of
that factor and the original closed immersion identifies the actual kernel
ideal, including its nonreduced structure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]

/-- The original factor to the original schematic image is schematically dominant. -/
theorem isSchemeTheoreticallyDominant_toImage : IsSchemeTheoreticallyDominant f.toImage := by
  constructor
  let U (i : Y.affineOpens) : f.image.affineOpens :=
    ⟨f.imageι ⁻¹ᵁ i, i.2.preimage f.imageι⟩
  apply IdealSheafData.ext_of_iSup_eq_top U
    (f.imageι.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y))
  intro i
  rw [Hom.ker_apply, IdealSheafData.ideal_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective i)

/-- Flat base change preserves the actual defining ideal of the schematic image. -/
theorem ker_pullback_snd_eq_comap_of_flat (g : T ⟶ Y) [Flat g] :
    (pullback.snd f g).ker = f.ker.comap g := by
  let J := (IsPullback.of_hasPullback g f.imageι).flip
  have H : IsPullback (pullback.fst f g) (pullback.snd f g)
      (f.toImage ≫ f.imageι) g := by
    rw [f.toImage_imageι]
    exact IsPullback.of_hasPullback f g
  let a := J.lift (pullback.fst f g ≫ f.toImage) (pullback.snd f g)
    (by rw [Category.assoc, f.toImage_imageι, pullback.condition])
  have ha : IsPullback (pullback.fst f g) a f.toImage (pullback.snd g f.imageι) :=
    IsPullback.of_bot' H J
  let : IsSchemeTheoreticallyDominant f.toImage := isSchemeTheoreticallyDominant_toImage f
  have : IsSchemeTheoreticallyDominant a := IsSchemeTheoreticallyDominant.of_isPullback ha
  have hc : a ≫ pullback.fst g f.imageι = pullback.snd f g := J.lift_snd _ _ _
  change (pullback.snd f g).ker = (pullback.fst g f.imageι).ker
  rw [← hc, Hom.ker_comp, a.ker_eq_bot, IdealSheafData.map_bot]

/-- The defining ideal comparison on an actual Cartesian square. -/
theorem ker_eq_comap_of_isPullback_of_flat {W : Scheme.{u}} {a : W ⟶ X} {j : W ⟶ T}
    (g : T ⟶ Y) [Flat g] (H : IsPullback a j f g) : j.ker = f.ker.comap g := by
  rw [← H.isoPullback_hom_snd, Hom.ker_comp_of_isIso]
  exact ker_pullback_snd_eq_comap_of_flat f g

/-- The canonical map between the original images in a flat Cartesian square. -/
def imageBaseChangeMapOfIsPullbackOfFlat {W : Scheme.{u}} {a : W ⟶ X} {j : W ⟶ T}
    (g : T ⟶ Y) [Flat g] (H : IsPullback a j f g) : j.image ⟶ f.image :=
  j.ker.subschemeMap f.ker g (IdealSheafData.le_map_iff_comap_le.mpr
    (ker_eq_comap_of_isPullback_of_flat f g H).symm.le)

/-- The comparison preserves the actual original image inclusions. -/
@[reassoc (attr := simp)]
theorem imageBaseChangeMap_of_isPullback_of_flat_imageι
    {W : Scheme.{u}} {a : W ⟶ X} {j : W ⟶ T}
    (g : T ⟶ Y) [Flat g] (H : IsPullback a j f g) :
    imageBaseChangeMapOfIsPullbackOfFlat f g H ≫ f.imageι = j.imageι ≫ g :=
  IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The actual image inclusions form a Cartesian square after flat base change. -/
theorem isPullback_imageι_of_isPullback_of_flat {W : Scheme.{u}} {a : W ⟶ X} {j : W ⟶ T}
    (g : T ⟶ Y) [Flat g] (H : IsPullback a j f g) :
    IsPullback j.imageι (imageBaseChangeMapOfIsPullbackOfFlat f g H) g f.imageι := by
  apply isPullback_of_isClosedImmersion
  · exact (imageBaseChangeMap_of_isPullback_of_flat_imageι f g H).symm
  · simpa only [imageι, IdealSheafData.ker_subschemeι] using
      (ker_eq_comap_of_isPullback_of_flat f g H).symm

/-- The comparison identifies the original image with its actual flat pullback. -/
def imageBaseChangeIsoOfFlat (g : T ⟶ Y) [Flat g] :
    (pullback.snd f g).image ≅ pullback g f.imageι :=
  (isPullback_imageι_of_isPullback_of_flat f g (IsPullback.of_hasPullback f g)).isoPullback

/-- The comparison preserves the actual inclusion of the original image. -/
@[reassoc (attr := simp)]
theorem imageBaseChangeIso_of_flat_hom_fst (g : T ⟶ Y) [Flat g] :
    (imageBaseChangeIsoOfFlat f g).hom ≫ pullback.fst g f.imageι =
      (pullback.snd f g).imageι :=
  (isPullback_imageι_of_isPullback_of_flat f g (IsPullback.of_hasPullback f g)).isoPullback_hom_fst

end AlgebraicGeometry.Scheme.Hom
