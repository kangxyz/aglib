/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Boundary.FiniteModels

/-!
# Projecting simultaneous boundary control to the original models

The canonical finite sum blowup supplies separated closed sets upstairs.
Closure control then chooses actual centres in each original model, avoiding
its entire protected open. All fibre products and original projections remain
literal; there is no schematic-image base-change assumption.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace
universe u v

namespace AlgebraicGeometry.Scheme.Compactification

/-- The closure of a closed subset of an open subscheme restricts to that subset. -/
theorem closure_image_closed_inter_open {X : Scheme.{u}}
    (V : X.Opens) (F : Closeds V.toScheme) :
    closure (V.ι '' (F : Set V.toScheme)) ∩ (V : Set X) = V.ι '' (F : Set V.toScheme) := by
  have hi : V.ι ⁻¹' (V.ι '' (F : Set V.toScheme)) = F :=
    Set.preimage_image_eq _ V.ι.isOpenEmbedding.injective
  have hc : V.ι ⁻¹' closure (V.ι '' (F : Set V.toScheme)) = F := by
    rw [V.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage V.ι.continuous,
      hi, F.isClosed.closure_eq]
  apply Set.Subset.antisymm
  · intro x hx
    have hh : (⟨x, hx.2⟩ : V.toScheme) ∈ V.ι ⁻¹'
        closure (V.ι '' (F : Set V.toScheme)) := hx.1
    rw [hc] at hh
    exact ⟨⟨x, hx.2⟩, hh, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨subset_closure ⟨x, hx, rfl⟩, x.property⟩

/-- Actual protected centres in all original models, with one uniform
upstairs boundary separation and uniform control for every subset `D`.
The common open `Ω` is retained as an actual unit locus of the upstairs
centre, so any original source inside it lifts unchanged. -/
theorem exists_projected_boundary_centres
    {M : Scheme.{u}} [IsNoetherian M] {ι : Type v} [Finite ι]
    {Y : ι → Scheme.{u}} [∀ i, IsNoetherian (Y i)] (π : ∀ i, M ⟶ Y i)
    (V : ∀ i, (Y i).Opens) (F : ∀ i, Closeds (V i).toScheme)
    (Ω : M.Opens) (hΩ : ∀ i, π i ⁻¹ᵁ V i = Ω)
    (hempty : (⋂ i, π i ⁻¹' ((V i).ι '' (F i : Set (V i).toScheme))) = ∅) :
    let E := fun i => π i ⁻¹' ((V i).ι '' (F i : Set (V i).toScheme))
    let K := fun i => IdealSheafData.vanishingIdeal (Closeds.closure (E i))
    let B := Blowup.blowupDatum (⨆ i, K i)
    (⨆ i, K i).comap Ω.ι = ⊤ ∧
    ∃ T : ι → Closeds B.Y,
      (⋂ i, (T i : Set B.Y)) = ∅ ∧
      ∀ i, ∃ I : (Y i).IdealSheafData,
        ((I.support : Set (Y i)) ⊆
          closure ((V i).ι '' (F i : Set (V i).toScheme)) \ (V i : Set (Y i))) ∧
        I.comap (V i).ι = ⊤ ∧
        let C := Blowup.blowupDatum I
        IsProper C.map ∧ IsIso (C.map ∣_ V i) ∧
        ∀ D : Set B.Y, D ⊆ (B.map ≫ π i) ⁻¹' (V i : Set (Y i)) →
          (pullback.snd (B.map ≫ π i) C.map ⁻¹'
            closure (C.map ⁻¹' ((V i).ι '' (F i : Set (V i).toScheme)))) ∩
            closure (pullback.fst (B.map ≫ π i) C.map ⁻¹' D) ⊆
              pullback.fst (B.map ≫ π i) C.map ⁻¹' (T i : Set B.Y) := by
  dsimp only
  let E := fun i => π i ⁻¹' ((V i).ι '' (F i : Set (V i).toScheme))
  let K := fun i => IdealSheafData.vanishingIdeal (Closeds.closure (E i))
  let B := Blowup.blowupDatum (⨆ i, K i)
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsLocallyNoetherian B.Y := LocallyOfFiniteType.isLocallyNoetherian B.map
  let : CompactSpace B.Y := QuasiCompact.compactSpace_of_compactSpace B.map
  let : IsNoetherian B.Y := ⟨⟩
  obtain ⟨hunit, T, hT, hboundary⟩ :=
    finite_model_boundary_separation π V F Ω hΩ hempty
  refine ⟨hunit, T, hT, ?_⟩
  intro i
  let Z₁ : Closeds (Y i) := Closeds.closure ((V i).ι '' (F i : Set (V i).toScheme))
  have he : (Z₁ : Set (Y i)) ∩ (V i : Set (Y i)) =
      (V i).ι '' (F i : Set (V i).toScheme) :=
    closure_image_closed_inter_open (V i) (F i)
  have hq : (B.map ≫ π i) ⁻¹' ((Z₁ : Set (Y i)) ∩ (V i : Set (Y i))) ⊆ T i := by
    rw [he]
    exact hboundary i
  obtain ⟨I, hsupp, hI, hp, hiso, hcontrol⟩ :=
    Blowup.exists_boundary_closure_control (B.map ≫ π i) (V i) Z₁ (T i) hq
  refine ⟨I, hsupp, hI, hp, hiso, ?_⟩
  intro D hD
  simpa only [he] using hcontrol D hD

end AlgebraicGeometry.Scheme.Compactification
