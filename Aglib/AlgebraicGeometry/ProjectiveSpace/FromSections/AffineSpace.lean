/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.AffineTuple
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The native affine-space inclusion and original coordinate tuples

The standard open immersion from Mathlib's relative affine space into
polynomial projective space is the ordinary section map of its native
coordinates. Composition retains the original morphism and its pulled
coordinate sections, rather than replacing it by a coordinate class.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.FromSections

variable (R : Type u) [CommRing R] (I : Type u) [Finite I]

/-- The standard affine-space inclusion, defined by the original native coordinates. -/
def affineSpaceInclusion : AffineSpace I (Spec (.of R)) ⟶ ProjectiveSpace R (Option I) :=
  AffineTuple.map (AffineSpace I (Spec (.of R)) ↘ Spec (.of R))
    (AffineSpace.coord (Spec (.of R)))

/-- On the polynomial spectrum this is exactly the original affine chart map. -/
@[reassoc]
theorem specIso_inv_affineSpaceInclusion :
    (AffineSpace.SpecIso I (.of R)).inv ≫ affineSpaceInclusion R I =
      AffineChart.map (MvPolynomial.C : R →+* MvPolynomial I R) MvPolynomial.X := by
  have hc : (AffineSpace.SpecIso I (.of R)).inv.appTop ∘
      AffineSpace.coord (Spec (.of R)) =
        (Scheme.ΓSpecIso (.of (MvPolynomial I R))).inv ∘ MvPolynomial.X := by
    funext i
    exact AffineSpace.SpecIso_inv_appTop_coord (.of R) i
  unfold affineSpaceInclusion
  rw [AffineTuple.map_naturality, AffineSpace.SpecIso_inv_over, hc]
  exact AffineTuple.map_spec _ _

/-- The native affine-space inclusion is the existing standard chart under
Mathlib's original polynomial-spectrum isomorphism. -/
theorem affineSpaceInclusion_eq :
    affineSpaceInclusion R I = (AffineSpace.SpecIso I (.of R)).hom ≫
      AffineChart.map (MvPolynomial.C : R →+* MvPolynomial I R) MvPolynomial.X := by
  calc
    _ = (AffineSpace.SpecIso I (.of R)).hom ≫
        (AffineSpace.SpecIso I (.of R)).inv ≫ affineSpaceInclusion R I := by simp
    _ = _ := by rw [specIso_inv_affineSpaceInclusion]

omit [Finite I] in
private theorem universalChartRingHom :
    AffineChart.ringHom (MvPolynomial.C : R →+* MvPolynomial I R) MvPolynomial.X =
      (optionCoordinateRingEquivPolynomial R I).toRingHom := by
  apply RingHom.ext
  intro q
  exact MvPolynomial.eval₂_eta (optionCoordinateRingEquivPolynomial R I q)

/-- The original standard projective chart, identified with Mathlib's actual
relative affine space using the original polynomial chart-ring equivalence. -/
def standardChartIsoAffineSpace :
    (coordinateOpen R (Option I) none).toScheme ≅ AffineSpace I (Spec (.of R)) :=
  ((AffineSpace.SpecIso I (.of R)) ≪≫
    Scheme.Spec.mapIso (optionCoordinateRingEquivPolynomial R I).toCommRingCatIso.op ≪≫
    (Proj.basicOpenIsoSpec (homogeneousSubmodule (Option I) R) (MvPolynomial.X none)
      (isHomogeneous_X R none) Nat.zero_lt_one).symm).symm

/-- The inverse chart identification retains exactly the original open inclusion. -/
@[reassoc]
theorem standardChartIsoAffineSpace_inv_ι :
    (standardChartIsoAffineSpace R I).inv ≫ (coordinateOpen R (Option I) none).ι =
      affineSpaceInclusion R I := by
  have h := (affineSpaceInclusion_eq R I).symm
  rw [AffineChart.map, universalChartRingHom] at h
  change ((AffineSpace.SpecIso I (.of R)).hom ≫
    Spec.map (CommRingCat.ofHom (optionCoordinateRingEquivPolynomial R I).toRingHom) ≫
    (Proj.basicOpenIsoSpec (homogeneousSubmodule (Option I) R) (MvPolynomial.X none)
      (isHomogeneous_X R none) Nat.zero_lt_one).inv) ≫
    (Proj.basicOpen (homogeneousSubmodule (Option I) R) (MvPolynomial.X none)).ι = _
  simpa only [Proj.awayι, Category.assoc] using h

/-- The forward chart identification also keeps the original inclusion triangle. -/
@[reassoc]
theorem standardChartIsoAffineSpace_hom_inclusion :
    (standardChartIsoAffineSpace R I).hom ≫ affineSpaceInclusion R I =
      (coordinateOpen R (Option I) none).ι := by
  rw [← standardChartIsoAffineSpace_inv_ι, Iso.hom_inv_id_assoc]

/-- This is an actual open immersion, not merely a pointwise chart parametrization. -/
instance affineSpaceInclusion_isOpenImmersion : IsOpenImmersion (affineSpaceInclusion R I) := by
  let e := optionCoordinateRingEquivPolynomial R I
  let : IsIso (CommRingCat.ofHom e.toRingHom) := by
    change IsIso e.toCommRingCatIso.hom
    infer_instance
  have h : IsOpenImmersion
      (AffineChart.map (MvPolynomial.C : R →+* MvPolynomial I R) MvPolynomial.X) := by
    rw [AffineChart.map, universalChartRingHom]
    infer_instance
  rw [affineSpaceInclusion_eq]
  infer_instance

/-- The inclusion is over the originally specified affine base. -/
@[reassoc]
theorem affineSpaceInclusion_toSpec :
    affineSpaceInclusion R I ≫ toSpec R (Option I) =
      AffineSpace I (Spec (.of R)) ↘ Spec (.of R) :=
  AffineTuple.map_toSpec _ _

variable {R I} {X : Scheme.{u}}

/-- Composition with the canonical inclusion is the tuple map of the
original pulled affine coordinates and original composite base morphism. -/
@[reassoc]
theorem comp_affineSpaceInclusion (f : X ⟶ AffineSpace I (Spec (.of R))) :
    f ≫ affineSpaceInclusion R I =
      AffineTuple.map (f ≫ AffineSpace I (Spec (.of R)) ↘ Spec (.of R))
        (f.appTop ∘ AffineSpace.coord (Spec (.of R))) :=
  AffineTuple.map_naturality _ _ _

/-- For a displayed morphism over the base, the equality uses exactly that
base map and the original affine coordinate sections. -/
theorem comp_affineSpaceInclusion_of_over
    (f : X ⟶ AffineSpace I (Spec (.of R))) (p : X ⟶ Spec (.of R))
    (hp : f ≫ AffineSpace I (Spec (.of R)) ↘ Spec (.of R) = p) :
    f ≫ affineSpaceInclusion R I =
      AffineTuple.map p (f.appTop ∘ AffineSpace.coord (Spec (.of R))) := by
  rw [comp_affineSpaceInclusion, hp]

end AlgebraicGeometry.ProjectiveSpace.FromSections
