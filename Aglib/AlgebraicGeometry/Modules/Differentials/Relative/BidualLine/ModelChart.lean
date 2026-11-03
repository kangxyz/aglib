/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.BirationalChartScalars
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.BidualLine.Affine
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.RingTheory.Kaehler.FractionRing


/-!
# Actual model-chart bidual lines from the original differential basis

The original finite-type coefficient map and the original birational model
supply all chart scalar and generic-rank data. The same coefficient ring is
retained throughout; no chart line, generic rank, common field certificate,
completeness or finite extension into a later local ring is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u


open AlgebraicGeometry.Scheme.FunctionField
open KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- Every actual nonempty affine chart of the regular surface model has the
actual top-form bidual line, with degree fixed by the original base basis. -/
theorem modelChart_bidualForms_isLocallyRankOne
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {Λ A R : CommRingCat.{u}} [IsDomain A] [IsDomain R]
    (ρ : Λ ⟶ A) (β : X ⟶ Spec A) [IsDominant β]
    [LocallyOfFiniteType (β ≫ Spec.map ρ)]
    (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))
    (hX : RegularStalks X) (hdX : topologicalKrullDim X ≤ 2)
    (j : Spec R ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential ρ)) :
    Invertible.IsLocallyRankOne (Spec R)
      ((show X.Modules from Invertible.dualSheaf X (Invertible.dualSheaf X
        (moduleExteriorPower X (relativeDifferentialSheaf (β ≫ Spec.map ρ)) n))).restrict j) := by
  let : IsLocallyNoetherian (Spec R) := LocallyOfFiniteType.isLocallyNoetherian j
  let : IsNoetherianRing R := isLocallyNoetherian_Spec.mp inferInstance
  let : IsRegularRing R := (regularStalks_spec_iff R).mp (hX.of_isOpenImmersion j)
  have hdR : ringKrullDim R ≤ 2 := by
    have h := j.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hdX
    change topologicalKrullDim (PrimeSpectrum R) ≤ 2 at h
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  let a := β ≫ Spec.map ρ
  let σ := Spec.preimage (j ≫ β)
  let α := Spec.preimage (j ≫ a)
  have hα : α = ρ ≫ σ := by
    dsimp only [α, a, σ]
    rw [← Category.assoc, Spec.preimage_comp, Spec.preimage_map]
  let K := (Spec R).functionField
  let : Algebra Λ R := α.hom.toAlgebra
  let : Algebra Λ K := ((algebraMap R K).comp α.hom).toAlgebra
  let : Algebra Λ A := ρ.hom.toAlgebra
  let : Algebra A K := ((algebraMap R K).comp σ.hom).toAlgebra
  let : IsFractionRing A K := modelChart_generic_isFractionRing β hβ j
  let : IsScalarTower Λ A K := by
    apply IsScalarTower.of_algebraMap_eq'
    change ((algebraMap R K).comp α.hom) =
      (((algebraMap R K).comp σ.hom).comp ρ.hom)
    rw [hα]
    rfl
  have hrank : Module.finrank K (KaehlerDifferential Λ K) = n := by
    simpa only [Fintype.card_fin] using
      (KaehlerDifferential.finrank_fraction_of_basis (K := K) b)
  exact affineBidualForms_isLocallyRankOne a j n K hdR hrank

end AlgebraicGeometry.Scheme.Modules.Differentials
