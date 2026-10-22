/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ChartEvaluation
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ChartConstants

/-!
# Surjectivity on the original product-coordinate opens

The original section map is identified with the native tensor chart-ring map.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.Segre

variable (R : Type u) [CommRing R] {ι κ : Type u}

theorem productChart_preimage_sourceOpen (a : ι) (b : κ) :
    ⊤ ≤ productChart R a b ⁻¹ᵁ sourceOpen (first R ι κ) (second R ι κ) (a, b) := by
  intro x _
  change productChart R a b x ∈
    (sourceOpen (first R ι κ) (second R ι κ) (a, b) : Set (product R ι κ))
  rw [← productChart_range]
  exact ⟨x, rfl⟩

theorem productSectionsIso_ratio_left (a : ι) (b : κ) (k : ι) :
    (productSectionsIso R a b).hom
      (ratioOn (first R ι κ) a k
        (sourceOpen (first R ι κ) (second R ι κ) (a, b)) inf_le_left) =
      Algebra.TensorProduct.includeLeftRingHom (coordinateRatio R ι a k) := by
  rw [productSectionsIso_hom R a b (productChart_preimage_sourceOpen R a b)]
  exact chart_pullback_ratio R (first R ι κ) a k _ inf_le_left _
    (productChart R a b) (productChart_preimage_sourceOpen R a b) _
    (productChart_first R a b)

theorem productSectionsIso_ratio_right (a : ι) (b : κ) (k : κ) :
    (productSectionsIso R a b).hom
      (ratioOn (second R ι κ) b k
        (sourceOpen (first R ι κ) (second R ι κ) (a, b)) inf_le_right) =
      Algebra.TensorProduct.includeRight (coordinateRatio R κ b k) := by
  rw [productSectionsIso_hom R a b (productChart_preimage_sourceOpen R a b)]
  exact chart_pullback_ratio R (second R ι κ) b k _ inf_le_right _
    (productChart R a b) (productChart_preimage_sourceOpen R a b) _
    (productChart_second R a b)

theorem productSectionsIso_coefficient (a : ι) (b : κ) (r : R) :
    (productSectionsIso R a b).hom
      (structuralCoefficient (first R ι κ ≫ toSpec R ι)
        (sourceOpen (first R ι κ) (second R ι κ) (a, b)) r) =
      algebraMap R (chartTensor R a b) r := by
  rw [productSectionsIso_hom R a b (productChart_preimage_sourceOpen R a b)]
  apply chart_pullback_constant
  rw [← Category.assoc, productChart_first, Category.assoc, factorChart_toSpec,
    ← Spec.map_comp]
  rfl

/-- The original section-ring map is the native tensor-ring map under the actual chart iso. -/
theorem productSectionsIso_comp_sectionChartHom (a : ι) (b : κ) :
    (productSectionsIso R a b).hom.hom.comp
        (sectionChartHom (first R ι κ) (second R ι κ) (a, b)) =
      chartRingHom R a b := by
  have hc (r : R) :
      ((productSectionsIso R a b).hom.hom.comp
          (sectionChartHom (first R ι κ) (second R ι κ) (a, b)))
        (coordinateRingCoefficient R (ι × κ) (a, b) r) =
      chartRingHom R a b (coordinateRingCoefficient R (ι × κ) (a, b) r) := by
    simp only [RingHom.comp_apply, sectionChartHom_coefficient, chartRingHom_coefficient]
    exact productSectionsIso_coefficient R a b r
  have hx (k : ι × κ) :
      ((productSectionsIso R a b).hom.hom.comp
          (sectionChartHom (first R ι κ) (second R ι κ) (a, b)))
        (coordinateRatio R (ι × κ) (a, b) k) =
      chartRingHom R a b (coordinateRatio R (ι × κ) (a, b) k) := by
    simp only [RingHom.comp_apply, sectionChartHom_ratio, sectionValue, map_mul,
      chartRingHom_ratio, chartValue]
    exact congrArg₂ (fun x y : chartTensor R a b => x * y)
      (productSectionsIso_ratio_left R a b k.1) (productSectionsIso_ratio_right R a b k.2)
  have he : ((productSectionsIso R a b).hom.hom.comp
        (sectionChartHom (first R ι κ) (second R ι κ) (a, b))).comp
        (polynomialToCoordinateRing R (ι × κ) (a, b)) =
      (chartRingHom R a b).comp (polynomialToCoordinateRing R (ι × κ) (a, b)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa using hc r
    · intro k
      simpa using hx k.1
  have he' := congrArg (fun q => q.comp (coordinateRingToPolynomial R (ι × κ) (a, b))) he
  simpa only [RingHom.comp_assoc, polynomialToCoordinateRing_comp_coordinateRingToPolynomial,
    RingHom.comp_id] using he'

/-- Surjectivity on the actual source sections, with no replacement-source hypothesis. -/
theorem sectionChartHom_surjective (a : ι) (b : κ) :
    Function.Surjective (sectionChartHom (first R ι κ) (second R ι κ) (a, b)) := by
  intro y
  obtain ⟨x, hx⟩ := chartRingHom_surjective R a b ((productSectionsIso R a b).hom y)
  refine ⟨x, (ConcreteCategory.bijective_of_isIso (productSectionsIso R a b).hom).1 ?_⟩
  rw [← productSectionsIso_comp_sectionChartHom] at hx
  exact hx

end AlgebraicGeometry.ProjectiveSpace.Segre
