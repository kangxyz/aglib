/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.Sections
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Original affine charts of the projective product

The native tensor spectrum maps into the original scheme pullback. Its range
is exactly the original intersection of inverse-image coordinate opens, and
both projection equations are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.Segre

variable (R : Type u) [CommRing R] (ι κ : Type u)

/-- The original scheme pullback of the two projective structure maps. -/
abbrev product := pullback (toSpec R ι) (toSpec R κ)

/-- The original first projection. -/
abbrev first : product R ι κ ⟶ ProjectiveSpace R ι := pullback.fst _ _

/-- The original second projection. -/
abbrev second : product R ι κ ⟶ ProjectiveSpace R κ := pullback.snd _ _

variable {ι κ}

/-- The native affine coordinate-chart inclusion. -/
abbrev factorChart {α : Type u} (a : α) :
    Spec (CommRingCat.of (coordinateRing R α a)) ⟶ ProjectiveSpace R α :=
  Proj.awayι (homogeneousSubmodule α R) (X a) (isHomogeneous_X R a) Nat.zero_lt_one

/-- Each original projective coordinate chart is an open immersion. -/
instance instIsOpenImmersionFactorChart {α : Type u} (a : α) :
    IsOpenImmersion (factorChart R a) :=
  Proj.instIsOpenImmersionAwayι (homogeneousSubmodule α R) (X a)
    (isHomogeneous_X R a) Nat.zero_lt_one

/-- The native factor chart has precisely the original coordinate-open range. -/
theorem factorChart_range {α : Type u} (a : α) :
    Set.range (factorChart R a) = (coordinateOpen R α a : Set (ProjectiveSpace R α)) :=
  congrArg (fun U : (ProjectiveSpace R α).Opens => (U : Set (ProjectiveSpace R α)))
    (Proj.opensRange_awayι (homogeneousSubmodule α R) (X a)
      (isHomogeneous_X R a) Nat.zero_lt_one)

/-- The native factor chart has the original coefficient algebra map to the base. -/
@[reassoc]
theorem factorChart_toSpec {α : Type u} (a : α) :
    factorChart R a ≫ toSpec R α =
      Spec.map (CommRingCat.ofHom (algebraMap R (coordinateRing R α a))) := by
  change Proj.awayι (homogeneousSubmodule α R) (X a)
    (isHomogeneous_X R a) Nat.zero_lt_one ≫ toSpec R α =
      Spec.map (CommRingCat.ofHom (coordinateRingCoefficient R α a))
  exact coordinateChart_toSpec R α a

/-- The canonical map of the actual affine-chart pullback into the original product. -/
def chartPullbackMap (a : ι) (b : κ) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R (coordinateRing R ι a))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (coordinateRing R κ b)))) ⟶ product R ι κ :=
  pullback.map _ _ _ _ (factorChart R a) (factorChart R b) (𝟙 _)
    (by rw [Category.comp_id]; exact (factorChart_toSpec R a).symm)
    (by rw [Category.comp_id]; exact (factorChart_toSpec R b).symm)

/-- The actual tensor-spectrum chart in the original product. -/
def productChart (a : ι) (b : κ) :
    Spec (CommRingCat.of (chartTensor R a b)) ⟶ product R ι κ :=
  (pullbackSpecIso R (coordinateRing R ι a) (coordinateRing R κ b)).inv ≫
    chartPullbackMap R a b

/-- The product of the original affine charts is an open immersion into the projective product. -/
instance instIsOpenImmersionChartPullbackMap (a : ι) (b : κ) :
    IsOpenImmersion (chartPullbackMap R a b) := by
  unfold chartPullbackMap
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion.{u}) inferInstance inferInstance
    (factorChart_toSpec R a).symm (factorChart_toSpec R b).symm

/-- The tensor-product coordinate chart is an open immersion into the projective product. -/
instance instIsOpenImmersionProductChart (a : ι) (b : κ) :
    IsOpenImmersion (productChart R a b) := by
  unfold productChart
  infer_instance

@[reassoc (attr := simp)]
theorem productChart_first (a : ι) (b : κ) :
    productChart R a b ≫ first R ι κ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ factorChart R a := by
  simp only [productChart, first, chartPullbackMap, Category.assoc,
    pullback.map, pullback.lift_fst, pullbackSpecIso_inv_fst_assoc]

@[reassoc (attr := simp)]
theorem productChart_second (a : ι) (b : κ) :
    productChart R a b ≫ second R ι κ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        coordinateRing R κ b →ₐ[R] chartTensor R a b).toRingHom) ≫ factorChart R b := by
  simp only [productChart, second, chartPullbackMap, Category.assoc,
    pullback.map, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc, AlgHom.toRingHom_eq_coe]

/-- The affine tensor chart has exactly the intended original product-chart range. -/
theorem productChart_range (a : ι) (b : κ) :
    Set.range (productChart R a b) =
      (sourceOpen (first R ι κ) (second R ι κ) (a, b) : Set (product R ι κ)) := by
  change Set.range ((chartPullbackMap R a b) ∘
    (pullbackSpecIso R (coordinateRing R ι a) (coordinateRing R κ b)).inv) = _
  rw [Set.range_comp,
    (pullbackSpecIso R (coordinateRing R ι a) (coordinateRing R κ b)).inv.surjective.range_eq,
    Set.image_univ]
  rw [chartPullbackMap, Scheme.Pullback.range_map, factorChart_range, factorChart_range]
  rfl

/-- The original product open, with its scheme structure, is the tensor spectrum. -/
def productOpenIsoSpec (a : ι) (b : κ) :
    (sourceOpen (first R ι κ) (second R ι κ) (a, b)).toScheme ≅
      Spec (CommRingCat.of (chartTensor R a b)) :=
  (IsOpenImmersion.isoOfRangeEq (productChart R a b)
    (sourceOpen (first R ι κ) (second R ι κ) (a, b)).ι
    ((productChart_range R a b).trans (Scheme.Opens.range_ι _).symm)).symm

@[reassoc (attr := simp)]
theorem productOpenIsoSpec_inv_ι (a : ι) (b : κ) :
    (productOpenIsoSpec R a b).inv ≫
      (sourceOpen (first R ι κ) (second R ι κ) (a, b)).ι = productChart R a b :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _
    ((productChart_range R a b).trans (Scheme.Opens.range_ι _).symm)

/-- The actual product-coordinate open is affine. -/
theorem isAffineOpen_sourceOpen (a : ι) (b : κ) :
    IsAffineOpen (sourceOpen (first R ι κ) (second R ι κ) (a, b)) :=
  IsAffine.of_isIso (productOpenIsoSpec R a b).hom

end AlgebraicGeometry.ProjectiveSpace.Segre
