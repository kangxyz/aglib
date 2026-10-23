/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.ChartMap
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Augmentation

/-!
# Native degree-one charts of the original coordinate augmentation

The graded polynomial presentation has the original specified linear denominator.
Its actual native chart retains every base coefficient and numerator. Transport
through an actual ring equivalence proves the corresponding original affine-chart
morphism; the concrete scalar Rees chart is a separate consumer.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TensorProduct HomogeneousLocalization
open MvPolynomial Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.ProjectiveSpace.FromSections

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.CoordinateAugmentation

open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.ProjectiveSpace.FromSections.Augmentation

section NativeChart

variable {R C ι : Type u} [CommRing R] [CommRing C] [Algebra R C]
  (u : ι →₀ R) (G : ℕ → Submodule R C) [GradedAlgebra G]
  (g : ι → C) (hg : Submodule.span R (Set.range g) = G 1)
  (hpow : ∀ n : ℕ, (G 1) ^ n = G n)
  (α : C) (hu : Finsupp.linearCombination R g u = α)

private def augmentedChartMap : coordinateRing R (Option ι) none →+* Away G α :=
  HomogeneousLocalization.map
    (Proj.DegreeOneEmbedding.presentation G (augmentedFamily u g)
      (augmentedFamily_span u G g hg) hpow) <| by
    rintro _ ⟨n, rfl⟩
    change (MvPolynomial.aeval (augmentedFamily u g)) (X none ^ n) ∈ Submonoid.powers α
    rw [map_pow, aeval_X]
    change Finsupp.linearCombination R g u ^ n ∈ Submonoid.powers α
    rw [hu]
    exact ⟨n, rfl⟩

private theorem augmentedChartMap_coefficient (r : R) :
    letI := Away.scalarAlgebra R G α
    augmentedChartMap u G g hg hpow α hu
        (coordinateRingCoefficient R (Option ι) none r) = algebraMap R (Away G α) r := by
  let := Away.scalarAlgebra R G α
  apply HomogeneousLocalization.val_injective
  change (Localization.mk ((MvPolynomial.aeval (augmentedFamily u g)) (MvPolynomial.C r))
      ⟨(MvPolynomial.aeval (augmentedFamily u g)) 1, _⟩ :
        Localization (Submonoid.powers α)) =
      Localization.mk (algebraMap R C r) ⟨1, _⟩
  simp only [aeval_C, map_one]

private theorem augmentedChartMap_ratio (hα : α ∈ G 1) (i : ι) :
    augmentedChartMap u G g hg hpow α hu
        (coordinateRatio R (Option ι) none (some i)) =
      Away.dehomogenize G hα (g i) := by
  have hgi : g i ∈ G 1 := by
    rw [← hg]
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [Away.dehomogenize_homogeneous G hα (g i) hgi]
  apply HomogeneousLocalization.val_injective
  change (Localization.mk ((MvPolynomial.aeval (augmentedFamily u g)) (X (some i)))
      ⟨(MvPolynomial.aeval (augmentedFamily u g)) (X none ^ 1), _⟩ :
        Localization (Submonoid.powers α)) =
      Localization.mk (g i) ⟨α ^ 1, _⟩
  simp only [map_pow, aeval_X, augmentedFamily, Option.elim, hu]

private theorem augmented_awayι_comp_embedding (hα : α ∈ G 1) :
    Proj.awayι G α hα Nat.zero_lt_one ≫
      Proj.DegreeOneEmbedding.embedding G (augmentedFamily u g)
        (augmentedFamily_span u G g hg) hpow =
    Spec.map (CommRingCat.ofHom (augmentedChartMap u G g hg hpow α hu)) ≫
      Proj.awayι (homogeneousSubmodule (Option ι) R) (X none)
        (isHomogeneous_X R none) Nat.zero_lt_one := by
  let F := Proj.DegreeOneEmbedding.presentation G (augmentedFamily u g)
    (augmentedFamily_span u G g hg) hpow
  have hF : F (X none) = α := by
    change (MvPolynomial.aeval (augmentedFamily u g)) (X none) = α
    rw [aeval_X]
    exact hu
  cases hF
  simpa only [Proj.DegreeOneEmbedding.embedding, F, augmentedChartMap, Away.map] using
    Proj.awayι_comp_map F
      (Proj.DegreeOneEmbedding.irrelevant_le_map G (augmentedFamily u g)
        (augmentedFamily_span u G g hg) hpow)
      Nat.zero_lt_one (X none) (isHomogeneous_X R none)

end NativeChart

private theorem optionChartHom_ext {R T ι : Type u} [CommRing R] [CommRing T]
    (φ ψ : coordinateRing R (Option ι) none →+* T)
    (hC : ∀ r, φ (coordinateRingCoefficient R (Option ι) none r) =
      ψ (coordinateRingCoefficient R (Option ι) none r))
    (hX : ∀ i, φ (coordinateRatio R (Option ι) none (some i)) =
      ψ (coordinateRatio R (Option ι) none (some i))) : φ = ψ := by
  have h : φ.comp (polynomialToCoordinateRing R (Option ι) none) =
      ψ.comp (polynomialToCoordinateRing R (Option ι) none) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, polynomialToCoordinateRing_C] using hC r
    · rintro ⟨i, hi⟩
      cases i with
      | none => exact (hi rfl).elim
      | some i =>
        simpa only [RingHom.comp_apply, polynomialToCoordinateRing_X] using hX i
  have h' := congrArg (fun q => q.comp (coordinateRingToPolynomial R (Option ι) none)) h
  simpa only [RingHom.comp_assoc, polynomialToCoordinateRing_comp_coordinateRingToPolynomial,
    RingHom.comp_id] using h'

private theorem augmentedChart_transport
    {R C T ι : Type u} [CommRing R] [CommRing C] [CommRing T] [Algebra R C]
    (u : ι →₀ R) (G : ℕ → Submodule R C) [GradedAlgebra G]
    (g : ι → C) (hg : Submodule.span R (Set.range g) = G 1)
    (hpow : ∀ n : ℕ, (G 1) ^ n = G n) (α : C)
    (hu : Finsupp.linearCombination R g u = α) (hα : α ∈ G 1)
    (E : T ≃+* Away G α) (β : R →+* T) (c : ι → T)
    (hbase : ∀ r, E (β r) = Proj.DegreeOneBaseChange.coefficientMap R G α r)
    (hcoord : ∀ i, E (c i) = Away.dehomogenize G hα (g i)) :
    E.symm.toRingHom.comp (augmentedChartMap u G g hg hpow α hu) =
      ProjectiveSpace.FromSections.AffineChart.ringHom β c := by
  let := Away.scalarAlgebra R G α
  apply optionChartHom_ext
  · intro r
    rw [RingHom.comp_apply, augmentedChartMap_coefficient,
      ProjectiveSpace.FromSections.AffineChart.ringHom_coefficient]
    apply E.injective
    change E (E.symm (algebraMap R (Away G α) r)) = E (β r)
    rw [RingEquiv.apply_symm_apply]
    exact (hbase r).symm
  · intro i
    rw [RingHom.comp_apply, augmentedChartMap_ratio u G g hg hpow α hu hα,
      ProjectiveSpace.FromSections.AffineChart.ringHom_ratio]
    apply E.injective
    change E (E.symm (Away.dehomogenize G hα (g i))) = E (c i)
    rw [RingEquiv.apply_symm_apply]
    exact (hcoord i).symm

/-- The original graded augmentation has the actual affine-chart map under the specified
ring equivalence and its proved coefficient and numerator equations. -/
theorem native_chart_augmentation
    {R C T ι : Type u} [CommRing R] [CommRing C] [CommRing T] [Algebra R C]
    (u : ι →₀ R) (G : ℕ → Submodule R C) [GradedAlgebra G]
    (g : ι → C) (hg : Submodule.span R (Set.range g) = G 1)
    (hpow : ∀ n : ℕ, (G 1) ^ n = G n) (α : C)
    (hu : Finsupp.linearCombination R g u = α) (hα : α ∈ G 1)
    (E : T ≃+* Away G α) (β : R →+* T) (c : ι → T)
    (hbase : ∀ r, E (β r) = Proj.DegreeOneBaseChange.coefficientMap R G α r)
    (hcoord : ∀ i, E (c i) = Away.dehomogenize G hα (g i)) :
    ScalarChartCoordinates.ringChartMap G α hα E ≫
      Proj.DegreeOneEmbedding.embedding G g hg hpow ≫ embedding u =
        ProjectiveSpace.FromSections.AffineChart.map β c := by
  unfold ScalarChartCoordinates.ringChartMap
  rw [Category.assoc, embedding_comp u G g hg hpow,
    augmented_awayι_comp_embedding u G g hg hpow α hu hα, ← Spec.map_comp_assoc]
  have hcat : CommRingCat.ofHom (augmentedChartMap u G g hg hpow α hu) ≫
      CommRingCat.ofHom E.symm.toRingHom =
      CommRingCat.ofHom (ProjectiveSpace.FromSections.AffineChart.ringHom β c) := by
    apply CommRingCat.hom_ext
    exact augmentedChart_transport u G g hg hpow α hu hα E β c hbase hcoord
  rw [hcat]
  rfl

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.CoordinateAugmentation
