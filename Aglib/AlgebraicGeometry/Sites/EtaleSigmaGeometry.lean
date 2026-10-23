/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct

/-!
# Actual disjoint component charts on the small-etale site of a coproduct

These charts retain the canonical scheme coproduct inclusions. Their covering
and disjointness are geometric facts about those inclusions, not hypotheses
on a substitute family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Etale

universe u

/-- The actual empty etale chart. -/
def emptyChart (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (Scheme.emptyTo X)

/-- The actual empty chart is initial in the original small-etale category. -/
def emptyChartIsInitial (X : Scheme.{u}) : IsInitial (emptyChart X) := by
  let : ∀ U : X.Etale, Unique (emptyChart X ⟶ U) := fun U =>
    { default := MorphismProperty.Over.homMk (Scheme.emptyTo U.left)
        (AlgebraicGeometry.emptyIsInitial.hom_ext _ _)
      uniq := fun f => by
        apply MorphismProperty.Over.Hom.ext
        exact AlgebraicGeometry.emptyIsInitial.hom_ext _ _ }
  exact IsInitial.ofUnique _

/-- Every initial etale chart has the actual initial underlying scheme. -/
def initialChartUnderlying {X : Scheme.{u}} (U : X.Etale) (hU : IsInitial U) :
    IsInitial U.left :=
  AlgebraicGeometry.emptyIsInitial.ofIso
    ((Etale.forget X ⋙ Over.forget X).mapIso ((emptyChartIsInitial X).uniqueUpToIso hU))

variable {ι : Type u} (Y : ι → Scheme.{u})

/-- The original component inclusion as an etale chart over the actual coproduct. -/
def sigmaChart (i : ι) : (∐ Y).Etale := Scheme.Etale.mk (Sigma.ι Y i)

/-- The literal component inclusion in the terminal chart. -/
def sigmaChartInclusion (i : ι) : sigmaChart Y i ⟶ Scheme.Etale.mk (𝟙 (∐ Y)) :=
  MorphismProperty.Over.homMk (Sigma.ι Y i) (Category.comp_id _)

/-- The actual component charts form a cocone at the terminal chart. -/
def sigmaChartCofan : Cofan (sigmaChart Y) :=
  Cofan.mk (Scheme.Etale.mk (𝟙 (∐ Y))) (sigmaChartInclusion Y)

instance sigmaChartInclusion_mono (i : ι) : Mono (sigmaChartInclusion Y i) := by
  apply Functor.mono_of_mono_map (Etale.forget (∐ Y) ⋙ Over.forget (∐ Y))
  exact inferInstanceAs (Mono (Sigma.ι Y i))

/-- Canonical component inclusions really cover the original coproduct etale site. -/
theorem sigmaCharts_cover :
    Sieve.ofArrows (sigmaChart Y) (sigmaChartInclusion Y) ∈
      (∐ Y).smallEtaleTopology (Scheme.Etale.mk (𝟙 (∐ Y))) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨⟨i, y⟩, rfl⟩ := (AlgebraicGeometry.sigmaMk Y).surjective x
  exact ⟨i, y, (AlgebraicGeometry.sigmaMk_mk Y i y).symm⟩

/-- Distinct canonical components have the actual initial etale intersection. -/
theorem sigmaCharts_disjoint [HasInitial (∐ Y).Etale] :
    Pairwise fun i j => IsPullback (initial.to _) (initial.to _)
      (sigmaChartInclusion Y i) (sigmaChartInclusion Y j) := by
  intro i j hij
  let F := Etale.forget (∐ Y) ⋙ Over.forget (∐ Y)
  let hI := initialChartUnderlying (⊥_ (∐ Y).Etale) initialIsInitial
  apply IsPullback.of_map F (initialIsInitial.hom_ext _ _)
  have h := CoproductDisjoint.isPullback_of_isInitial (coproductIsCoproduct Y) hI hij
  change IsPullback (initial.to (sigmaChart Y i)).left
    (initial.to (sigmaChart Y j)).left (Sigma.ι Y i) (Sigma.ι Y j)
  rw [hI.hom_ext (initial.to (sigmaChart Y i)).left (hI.to (Y i)),
    hI.hom_ext (initial.to (sigmaChart Y j)).left (hI.to (Y j))]
  exact h

end AlgebraicGeometry.Scheme.Etale
