/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSigmaGeometry
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.DisjointSections

/-!
# Original abelian sheaf sections on a scheme coproduct

The bijection is the literal restriction along the canonical component charts.
The coefficient universe is arbitrary subject only to the native smallness of
the component index for forming its section product.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Etale

universe u v

variable {ι : Type u} (Y : ι → Scheme.{u})

/-- The empty family covers the actual empty chart in the original etale topology. -/
theorem emptyChart_empty_cover (X : Scheme.{u}) :
    Sieve.ofArrows (fun i : Empty => Empty.elim i)
      (fun i : Empty => (Empty.elim i : Empty.elim i ⟶ emptyChart X)) ∈
      X.smallEtaleTopology (emptyChart X) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  change (∅ : Scheme.{u}) at x
  exact isEmptyElim x

/-- Actual abelian sheaf sections decompose by the original component restrictions. -/
theorem sigmaSections_bijective [Small.{v} ι]
    (F : Sheaf (∐ Y).smallEtaleTopology AddCommGrpCat.{v}) :
    Function.Bijective (fun x : F.obj.obj (op (Scheme.Etale.mk (𝟙 (∐ Y)))) =>
      fun i => F.obj.map (sigmaChartInclusion Y i).op x) := by
  let : HasInitial (∐ Y).Etale := (emptyChartIsInitial (∐ Y)).hasInitial
  let : ∀ i, Mono ((sigmaChartCofan Y).inj i) :=
    fun i => inferInstanceAs (Mono (sigmaChartInclusion Y i))
  have hF : Presieve.IsSheaf (∐ Y).smallEtaleTopology
      (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v}) := by
    apply (isSheaf_iff_isSheaf_of_type _ _).mp
    exact ((sheafCompose (∐ Y).smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{v})).obj F).property
  exact Sheaf.LargeCohomology.disjointSections_bijective
    (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v}) (emptyChartIsInitial (∐ Y))
    (hF.isSheafFor _ (by
      simpa only [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty] using
        emptyChart_empty_cover (∐ Y)))
    (sigmaChartCofan Y) (sigmaCharts_disjoint Y)
    (hF.isSheafFor _ (sigmaCharts_cover Y))

end AlgebraicGeometry.Scheme.Etale
