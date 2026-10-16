/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.ChartPullback

/-!
# Arbitrary base change of actual polynomial projective space

The original projective coefficient morphism and the original structural maps
form a Cartesian square for every coefficient ring homomorphism. The proof
uses the original standard affine charts and their native polynomial pushouts.
The resulting isomorphism has the original pair of morphisms as its forward map.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Polynomial projective space commutes with every original coefficient-ring base change. -/
theorem isPullback_map (f : R →+* S) (ι : Type u) :
    IsPullback (map f ι) (toSpec S ι) (toSpec R ι) (Spec.map (CommRingCat.ofHom f)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (coordinateAffineOpenCover R ι).openCover
  intro i
  change ι at i
  let aR := Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one
  let H := (coordinateRingMap_awayι_isPullback f ι i).flip
  change IsPullback (pullback.snd (map f ι) aR)
    (pullback.fst (map f ι) aR ≫ toSpec S ι) (aR ≫ toSpec R ι)
      (Spec.map (CommRingCat.ofHom f))
  refine (coordinateRingMap_isPullback f ι i).of_iso H.isoPullback
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.refl_hom, Category.comp_id] using H.isoPullback_hom_snd.symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, H.isoPullback_hom_fst]
    exact (coordinateChart_toSpec S ι i).symm
  · simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp,
      coordinateRingCoefficient, aR] using
      (coordinateChart_toSpec R ι i).symm
  · simp

/-- The actual polynomial projective scheme over the new ring is the native fiber product. -/
def baseChangeIso (f : R →+* S) (ι : Type u) :
    ProjectiveSpace S ι ≅ pullback (toSpec R ι) (Spec.map (CommRingCat.ofHom f)) :=
  (isPullback_map f ι).isoPullback

@[reassoc (attr := simp)]
theorem baseChangeIso_hom_fst (f : R →+* S) (ι : Type u) :
    (baseChangeIso f ι).hom ≫ pullback.fst (toSpec R ι) (Spec.map (CommRingCat.ofHom f)) =
      map f ι :=
  (isPullback_map f ι).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem baseChangeIso_hom_snd (f : R →+* S) (ι : Type u) :
    (baseChangeIso f ι).hom ≫ pullback.snd (toSpec R ι) (Spec.map (CommRingCat.ofHom f)) =
      toSpec S ι :=
  (isPullback_map f ι).isoPullback_hom_snd

/-- The forward map is exactly the canonical native comparison of the original square. -/
theorem baseChangeIso_hom (f : R →+* S) (ι : Type u) :
    (baseChangeIso f ι).hom = pullback.lift (map f ι) (toSpec S ι) (map_toSpec f ι) := by
  apply pullback.hom_ext <;> simp

end AlgebraicGeometry.ProjectiveSpace
