/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsEtaleSectionFactor
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseOpenBaseChange

/-! # The unchanged finite-etale section extends as an open section

The idempotent factor constructs a section of the original affine map,
retaining its exact restriction triangle and etaleness at every image point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- Hartogs scalar identifications extend the original finite-etale section
as an open section of the unchanged affine morphism. -/
theorem exists_open_section_of_hartogsScalar
    {B C : Type u} [CommRing B] [CommRing C] {X Y : Scheme.{u}}
    (α : X ⟶ Spec (.of B)) (β : Y ⟶ Spec (.of C))
    [QuasiCompact β] [QuasiSeparated β]
    (τ : B →+* C) (r : Y ⟶ X) [IsFinite r] [Etale r]
    (h : r ≫ α = β ≫ Spec.map (CommRingCat.ofHom τ))
    (hα : Function.Bijective (affineScalarMap α))
    (hβ : Function.Bijective (affineScalarMap β))
    (s : X ⟶ Y) (hs : s ≫ r = 𝟙 X) :
    ∃ t : Spec (.of B) ⟶ Spec (.of C),
      t ≫ Spec.map (CommRingCat.ofHom τ) = 𝟙 (Spec (.of B)) ∧
      α ≫ t = s ≫ β ∧ IsOpenImmersion t ∧
      ∀ x : Spec (.of B), (Spec.map (CommRingCat.ofHom τ)).etaleAt (t x) := by
  obtain ⟨e, _, he, hfactor⟩ :=
    exists_idempotent_sectionFactor_isIso α β τ r h hα hβ s hs
  let loc := Spec.algebraMap C (Localization.Away e)
  let f := Spec.map (CommRingCat.ofHom τ)
  let : IsIso (loc ≫ f) := hfactor
  let t := inv (loc ≫ f) ≫ loc
  have ht : t ≫ f = 𝟙 (Spec (.of B)) := by
    dsimp only [t]
    rw [Category.assoc, IsIso.inv_hom_id]
  have hloc : Set.range loc = (PrimeSpectrum.basicOpen e).carrier :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away e) e
  have hrange : Set.range (s ≫ β) ⊆ Set.range loc := by
    rintro _ ⟨x, rfl⟩
    rw [hloc]
    have hx : s x ∈ β ⁻¹' (PrimeSpectrum.basicOpen e).carrier :=
      he.symm ▸ (show s x ∈ Set.range s from ⟨x, rfl⟩)
    exact hx
  let l := IsOpenImmersion.lift loc (s ≫ β) hrange
  have hl : l ≫ loc = s ≫ β := IsOpenImmersion.lift_fac loc (s ≫ β) hrange
  have hlf : l ≫ (loc ≫ f) = α := by
    rw [← Category.assoc, hl, Category.assoc, ← h, ← Category.assoc, hs,
      Category.id_comp]
  have hmatch : α ≫ t = s ≫ β := by
    rw [← hlf]
    dsimp only [t]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hl
  let : IsOpenImmersion t := inferInstance
  refine ⟨t, ht, hmatch, inferInstance, ?_⟩
  intro x
  apply Hom.etaleAt.of_comp_openImmersion t f x
  refine ⟨⊤, trivial, ?_⟩
  rw [ht]
  infer_instance

end AlgebraicGeometry.Scheme
