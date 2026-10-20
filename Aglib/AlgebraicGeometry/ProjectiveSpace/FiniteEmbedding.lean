/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

/-
Copyright (c) 2026 R5Lab contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding.Coefficients
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding.Map
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Reindex
public import Mathlib.Data.Fintype.EquivFin

/-!
# Projective embeddings of finite covers of projective space

For a finite morphism to finite-coordinate polynomial projective space, the actual
finite direct image supplies the coefficients of a projective embedding of the
original source. The chart construction, its overlap equations and its structural
factorization are those of `FiniteEmbedding.Map`. The selected coordinate opens
cover the image; native locality gives an immersion, and properness makes it closed.

The final theorem reindexes the finite nonempty coordinate set to `ULift (Fin (n+1))`
over the original base ring. It works over every commutative ring, with no
Noetherianity hypothesis or supplied generator datum. The intended upstream owner
is `Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding`; its current consumer
is the original proper-curve projective embedding in R5Lab.

Authoring basis: project `5b493a5709ba2e4242f94cf163611602c03f3cf3`,
Aglib `197ca0728db3cdf1552a6bcefeeda901e3377862`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1.
-/




@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding

variable {R : Type u} [CommRing R] {ι : Type u} {Y : Scheme.{u}}

/-- The actual chart construction is an immersion for every finite original map. -/
theorem map_isImmersion (f : Y ⟶ ProjectiveSpace R ι) (D : ChartData f)
    [IsFinite f] : IsImmersion (map f D) := by
  let V := fun i => coordinateOpen R (Coordinate f D) (distinguished f D i)
  have hlocal (i : ι) : IsClosedImmersion (map f D ∣_ V i) := by
    let e := Y.isoOfEq (map_preimage_selected f D i)
    have hfac : map f D ∣_ V i = e.hom ≫ chartMap f D i := by
      apply (cancel_mono (V i).ι).mp
      rw [morphismRestrict_ι, Category.assoc]
      change _ = e.hom ≫ localMap f D i
      rw [← ι_map f D i, ← Category.assoc]
      change _ = (Y.isoOfEq (map_preimage_selected f D i)).hom ≫
        (sourceOpen f i).ι ≫ map f D
      rw [Scheme.isoOfEq_hom_ι_assoc]
    rw [hfac]
    have := chartMap_isClosedImmersion f D i
    infer_instance
  let : MorphismProperty.RespectsRight (@IsImmersion) (@IsOpenImmersion) := {
    postcomp := fun i hi g hg => by
      have := hi
      have := hg
      infer_instance }
  apply IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) V
  · rintro _ ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ ⨆ i, sourceOpen f i by rw [iSup_sourceOpen_eq_top]; trivial)
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    change x ∈ map f D ⁻¹ᵁ V i
    rwa [map_preimage_selected]
  · intro i
    have := hlocal i
    infer_instance

/-- Finite coordinates make the source proper over the base and its actual
projective-coordinate map a closed immersion. -/
theorem map_isClosedImmersion [Finite ι]
    (f : Y ⟶ ProjectiveSpace R ι) (D : ChartData f) [IsFinite f] :
    IsClosedImmersion (map f D) := by
  have := map_isImmersion f D
  have : IsProper (map f D ≫ toSpec R (Coordinate f D)) := by
    rw [map_toSpec]
    infer_instance
  have : IsProper (map f D) := IsProper.of_comp _ (toSpec R (Coordinate f D))
  exact IsClosedImmersion.of_isPreimmersion _ (map f D).isClosedMap.isClosed_range

private theorem exists_finiteCoordinateEquiv (α : Type u) [Finite α] [Nonempty α] :
    ∃ n : ℕ, Nonempty (α ≃ ULift.{u} (Fin (n + 1))) := by
  let := Fintype.ofFinite α
  let n := Fintype.card α - 1
  have hpos : 0 < Fintype.card α := Fintype.card_pos
  have hc : Fintype.card α = n + 1 := (Nat.sub_add_cancel hpos).symm
  exact ⟨n, ⟨(Fintype.equivFinOfCardEq hc).trans Equiv.ulift.symm⟩⟩

/-- A finite cover of projective space has an actual closed embedding into finite
standard polynomial projective space over the unchanged commutative base ring. -/
theorem exists_closedImmersion_of_isFinite [Finite ι] [Nonempty ι]
    (f : Y ⟶ ProjectiveSpace R ι) [IsFinite f] :
    ∃ (n : ℕ) (j : Y ⟶ ProjectiveSpace R (ULift.{u} (Fin (n + 1)))),
      IsClosedImmersion j ∧ j ≫ toSpec R (ULift.{u} (Fin (n + 1))) =
        f ≫ toSpec R ι := by
  let D := chartDataOfFinite f
  have := map_isClosedImmersion f D
  obtain ⟨n, ⟨e⟩⟩ := exists_finiteCoordinateEquiv (Coordinate f D)
  refine ⟨n, map f D ≫ (reindexIso R e).hom, inferInstance, ?_⟩
  have he := reindexIso_hom_toSpec R e
  change (reindexIso R e).hom ≫ toSpec R (ULift.{u} (Fin (n + 1))) =
    toSpec R (Coordinate f D) at he
  rw [Category.assoc, he, map_toSpec]

end AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding
