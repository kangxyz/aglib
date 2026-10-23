/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.FiniteProduct
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Reindex

/-!
# Composing actual closed projective embeddings through Segre

A closed map to the pullback of projective space over an already embedded base
composes with the original binary Segre embedding. Both product projections and
the original coefficient triangle are retained. Finite reindexing includes empty
coordinate sets; a nonempty source supplies the positive-coordinate condition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Segre

variable (R : Type u) [CommRing R] (ι κ : Type u)
  {W Y : Scheme.{u}}

/-- The actual base map induces the native map to the ordered Segre product.
The projective-space projection is first and the embedded base is second. -/
def baseEmbeddingProductMap (a : W ⟶ Spec (CommRingCat.of R))
    (j : W ⟶ ProjectiveSpace R κ) (hj : j ≫ toSpec R κ = a) :
    pullback a (toSpec R ι) ⟶ product R ι κ :=
  (pullbackSymmetry a (toSpec R ι)).hom ≫
    pullback.map (toSpec R ι) a (toSpec R ι) (toSpec R κ)
      (𝟙 _) j (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans hj.symm)

@[reassoc (attr := simp)]
theorem baseEmbeddingProductMap_first (a : W ⟶ Spec (CommRingCat.of R))
    (j : W ⟶ ProjectiveSpace R κ) (hj : j ≫ toSpec R κ = a) :
    baseEmbeddingProductMap R ι κ a j hj ≫ first R ι κ =
      pullback.snd a (toSpec R ι) := by
  simp [baseEmbeddingProductMap, first, pullback.map, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem baseEmbeddingProductMap_second (a : W ⟶ Spec (CommRingCat.of R))
    (j : W ⟶ ProjectiveSpace R κ) (hj : j ≫ toSpec R κ = a) :
    baseEmbeddingProductMap R ι κ a j hj ≫ second R ι κ =
      pullback.fst a (toSpec R ι) ≫ j := by
  simp [baseEmbeddingProductMap, second, pullback.map, pullback.lift_snd]

/-- Closedness is preserved by this actual product map. -/
instance isClosedImmersion_baseEmbeddingProductMap
    (a : W ⟶ Spec (CommRingCat.of R)) (j : W ⟶ ProjectiveSpace R κ)
    (hj : j ≫ toSpec R κ = a) [IsClosedImmersion j] :
    IsClosedImmersion (baseEmbeddingProductMap R ι κ a j hj) := by
  let : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion.{u}) :=
    { comp_mem := fun f g hf hg ↦ @IsClosedImmersion.comp _ _ _ f g hf hg }
  dsimp only [baseEmbeddingProductMap]
  exact @IsClosedImmersion.comp _ _ _ _ _
    (@IsClosedImmersion.instOfIsIsoScheme _ _ _ (Iso.isIso_hom _))
    (MorphismProperty.pullbackMap (P := @IsClosedImmersion.{u}) inferInstance inferInstance
      (Category.id_comp _).symm hj.symm)

/-- The unchanged source maps to projective space by its given closed map,
the given embedding of the base, and the original binary Segre embedding. -/
def closedCompositionMap (a : W ⟶ Spec (CommRingCat.of R))
    (j : W ⟶ ProjectiveSpace R κ) (hj : j ≫ toSpec R κ = a)
    (h : Y ⟶ pullback a (toSpec R ι)) : Y ⟶ ProjectiveSpace R (ι × κ) :=
  h ≫ baseEmbeddingProductMap R ι κ a j hj ≫ embedding R ι κ

instance isClosedImmersion_closedCompositionMap
    (a : W ⟶ Spec (CommRingCat.of R)) (j : W ⟶ ProjectiveSpace R κ)
    (hj : j ≫ toSpec R κ = a) (h : Y ⟶ pullback a (toSpec R ι))
    [IsClosedImmersion j] [IsClosedImmersion h] :
    IsClosedImmersion (closedCompositionMap R ι κ a j hj h) := by
  dsimp only [closedCompositionMap]
  infer_instance

/-- The composite retains the original structure map through the first
projection of the original pullback over the base scheme. -/
@[reassoc (attr := simp)]
theorem closedCompositionMap_toSpec (a : W ⟶ Spec (CommRingCat.of R))
    (j : W ⟶ ProjectiveSpace R κ) (hj : j ≫ toSpec R κ = a)
    (h : Y ⟶ pullback a (toSpec R ι)) :
    closedCompositionMap R ι κ a j hj h ≫ toSpec R (ι × κ) =
      h ≫ pullback.fst a (toSpec R ι) ≫ a := by
  calc
    closedCompositionMap R ι κ a j hj h ≫ toSpec R (ι × κ) =
        h ≫ pullback.snd a (toSpec R ι) ≫ toSpec R ι := by
      simp only [closedCompositionMap, Category.assoc, embedding_toSpec,
        baseEmbeddingProductMap_first_assoc]
    _ = h ≫ pullback.fst a (toSpec R ι) ≫ a :=
      congrArg (fun k ↦ h ≫ k) (pullback.condition (f := a) (g := toSpec R ι)).symm

/-- Explicit coordinate reindexing preserves the same coefficient triangle. -/
@[reassoc]
theorem closedCompositionMap_reindex_toSpec {τ : Type u} (e : (ι × κ) ≃ τ)
    (a : W ⟶ Spec (CommRingCat.of R)) (j : W ⟶ ProjectiveSpace R κ)
    (hj : j ≫ toSpec R κ = a) (h : Y ⟶ pullback a (toSpec R ι)) :
    (closedCompositionMap R ι κ a j hj h ≫ (reindexIso R e).hom) ≫ toSpec R τ =
      h ≫ pullback.fst a (toSpec R ι) ≫ a := by
  have he := reindexIso_hom_toSpec R e
  change (reindexIso R e).hom ≫ toSpec R τ = toSpec R (ι × κ) at he
  rw [Category.assoc, he, closedCompositionMap_toSpec]

/-- A finite coordinate reindex exists even when its coordinate set is empty. -/
theorem exists_finite_reindex_closedCompositionMap [Finite ι] [Finite κ]
    (a : W ⟶ Spec (CommRingCat.of R)) (j : W ⟶ ProjectiveSpace R κ)
    (hj : j ≫ toSpec R κ = a) (h : Y ⟶ pullback a (toSpec R ι))
    [IsClosedImmersion j] [IsClosedImmersion h] :
    ∃ (n : ℕ) (e : (ι × κ) ≃ ULift.{u} (Fin n)),
      IsClosedImmersion (closedCompositionMap R ι κ a j hj h ≫ (reindexIso R e).hom) ∧
        (closedCompositionMap R ι κ a j hj h ≫ (reindexIso R e).hom) ≫
            toSpec R (ULift.{u} (Fin n)) = h ≫ pullback.fst a (toSpec R ι) ≫ a := by
  classical
  let := Fintype.ofFinite (ι × κ)
  let e := (Fintype.equivFin (ι × κ)).trans Equiv.ulift.symm
  exact ⟨Fintype.card (ι × κ), e, inferInstance,
    closedCompositionMap_reindex_toSpec R ι κ e a j hj h⟩

omit ι κ in
/-- A nonempty actual source mapping to projective space supplies a coordinate,
using the original standard-open cover. -/
theorem nonempty_coordinates_of_nonempty_source {α : Type u} [Nonempty Y]
    (f : Y ⟶ ProjectiveSpace R α) : Nonempty α := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  have hy : f y ∈ ⨆ i, coordinateOpen R α i := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨i⟩

/-- For a nonempty actual source, positive finite standard coordinates are
derived from its actual Segre map, without assumptions on either index set. -/
theorem exists_positive_reindex_closedCompositionMap [Finite ι] [Finite κ] [Nonempty Y]
    (a : W ⟶ Spec (CommRingCat.of R)) (j : W ⟶ ProjectiveSpace R κ)
    (hj : j ≫ toSpec R κ = a) (h : Y ⟶ pullback a (toSpec R ι))
    [IsClosedImmersion j] [IsClosedImmersion h] :
    ∃ (n : ℕ) (e : (ι × κ) ≃ ULift.{u} (Fin (n + 1))),
      IsClosedImmersion (closedCompositionMap R ι κ a j hj h ≫ (reindexIso R e).hom) ∧
        (closedCompositionMap R ι κ a j hj h ≫ (reindexIso R e).hom) ≫
            toSpec R (ULift.{u} (Fin (n + 1))) = h ≫ pullback.fst a (toSpec R ι) ≫ a := by
  classical
  let : Nonempty (ι × κ) := nonempty_coordinates_of_nonempty_source R
    (closedCompositionMap R ι κ a j hj h)
  let := Fintype.ofFinite (ι × κ)
  let n := Fintype.card (ι × κ) - 1
  have hpos : 0 < Fintype.card (ι × κ) := Fintype.card_pos
  have hc : Fintype.card (ι × κ) = n + 1 := (Nat.sub_add_cancel hpos).symm
  let e := (Fintype.equivFinOfCardEq hc).trans Equiv.ulift.symm
  exact ⟨n, e, inferInstance, closedCompositionMap_reindex_toSpec R ι κ e a j hj h⟩

end AlgebraicGeometry.ProjectiveSpace.Segre
