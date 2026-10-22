/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.Sections
public import Aglib.AlgebraicGeometry.ProjectiveSpace.ChartGluing

/-!
# The original Segre morphism

The product-coordinate morphism is glued on the actual inverse-image opens.
Its exact coordinate-open preimages and unchanged structural map are retained.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.Segre

variable {R : Type u} [CommRing R] {ι κ : Type u} {Y : Scheme.{u}}
  (f : Y ⟶ ProjectiveSpace R ι) (g : Y ⟶ ProjectiveSpace R κ)

/-- The original product-coordinate maps agree on the original double overlaps. -/
theorem sectionChartHom_compatible :
    ChartGluing.Compatible (sourceOpen f g) (sectionChartHom f g) where
  coefficient a b r := by
    simp only [ChartGluing.restrict, RingHom.comp_apply, sectionChartHom_coefficient,
      structuralCoefficient_restrict]
  ratio a b k := by
    simpa only [ChartGluing.restrict, RingHom.comp_apply, sectionChartHom_ratio] using
      sectionValue_overlap f g a b k

/-- The actual projective morphism with coordinates the products of factor coordinates. -/
def map : Y ⟶ ProjectiveSpace R (ι × κ) :=
  ChartGluing.map (sourceOpen f g) (sectionChartHom f g)
    (sectionChartHom_compatible f g) (iSup_sourceOpen_eq_top f g)

@[reassoc (attr := simp)]
theorem ι_map (a : ι × κ) : (sourceOpen f g a).ι ≫ map f g =
    ChartGluing.localMap (sourceOpen f g) (sectionChartHom f g) a :=
  ChartGluing.ι_map _ _ _ _ a

/-- Exact inverse images of the original target-coordinate opens. -/
theorem map_preimage_coordinateOpen (a : ι × κ) :
    map f g ⁻¹ᵁ coordinateOpen R (ι × κ) a = sourceOpen f g a :=
  ChartGluing.map_preimage_coordinateOpen _ _ _ _
    (fun a b => by rw [sectionChartHom_ratio, basicOpen_sectionValue]) a

/-- The product-coordinate morphism has exactly the original base morphism. -/
@[reassoc]
theorem map_toSpec : map f g ≫ toSpec R (ι × κ) = f ≫ toSpec R ι := by
  apply (ChartGluing.cover (sourceOpen f g) (iSup_sourceOpen_eq_top f g)).hom_ext
  intro a
  change ι × κ at a
  change (sourceOpen f g a).ι ≫ (map f g ≫ _) = (sourceOpen f g a).ι ≫ _
  rw [← Category.assoc, ι_map, ChartGluing.localMap]
  simp only [Category.assoc]
  rw [coordinateChart_toSpec, ← Spec.map_comp]
  have hc : CommRingCat.ofHom (algebraMap R (coordinateRing R (ι × κ) a)) ≫
      CommRingCat.ofHom (sectionChartHom f g a) =
      CommRingCat.ofHom (structuralCoefficient (f ≫ toSpec R ι) (sourceOpen f g a)) := by
    ext r
    exact sectionChartHom_coefficient f g a r
  change (sourceOpen f g a).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (coordinateRing R (ι × κ) a)) ≫
      CommRingCat.ofHom (sectionChartHom f g a)) = _
  rw [hc]
  exact structuralCoefficient_toSpec _ _

end AlgebraicGeometry.ProjectiveSpace.Segre
