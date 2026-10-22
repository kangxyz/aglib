/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.BoundarySeparation.Finite
public import Aglib.AlgebraicGeometry.Blowup.BoundarySeparation.ClosureControl

/-!
# Simultaneous boundary separation for normalized models

On a common open domain, the actual inverse-image boundaries are relatively
closed. Their closures define a canonical finite sum centre. Blowing it up
separates closed sets containing all the original inverse-image boundaries.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace
universe u v

namespace AlgebraicGeometry.Scheme.Compactification

/-- The canonical boundary blowup for actual model projections.
Equality of the open domains will be supplied by uniqueness of their closed
graphs on the original product image. -/
theorem finite_model_boundary_separation
    {M : Scheme.{u}} {ι : Type v}
    {Y : ι → Scheme.{u}} (π : ∀ i, M ⟶ Y i)
    (V : ∀ i, (Y i).Opens) (F : ∀ i, Closeds (V i).toScheme)
    (Ω : M.Opens) (hΩ : ∀ i, π i ⁻¹ᵁ V i = Ω)
    (hempty : (⋂ i, π i ⁻¹' ((V i).ι '' (F i : Set (V i).toScheme))) = ∅) :
    let E := fun i => π i ⁻¹' ((V i).ι '' (F i : Set (V i).toScheme))
    let K := fun i => IdealSheafData.vanishingIdeal (Closeds.closure (E i))
    let B := Blowup.blowupDatum (⨆ i, K i)
    (⨆ i, K i).comap Ω.ι = ⊤ ∧
    ∃ T : ι → Closeds B.Y,
      (⋂ i, (T i : Set B.Y)) = ∅ ∧
      ∀ i, (B.map ≫ π i) ⁻¹' ((V i).ι '' (F i : Set (V i).toScheme)) ⊆ T i := by
  dsimp only
  let E := fun i => π i ⁻¹' ((V i).ι '' (F i : Set (V i).toScheme))
  let K := fun i => IdealSheafData.vanishingIdeal (Closeds.closure (E i))
  let B := Blowup.blowupDatum (⨆ i, K i)
  have hEΩ : ∀ i, E i ⊆ Ω := by
    intro i x hx
    rw [← hΩ i]
    obtain ⟨z, _, hz⟩ := hx
    change π i x ∈ V i
    rw [← hz]
    exact z.property
  have hclosed : ∀ i, IsClosed (Ω.ι ⁻¹' E i) := by
    intro i
    let r : Ω.toScheme → (V i).toScheme := fun x =>
      ⟨π i x.val, by
        change x.val ∈ π i ⁻¹ᵁ V i
        rw [hΩ i]
        exact x.property⟩
    have hr : Continuous r :=
      ((π i).continuous.comp continuous_subtype_val).subtype_mk _
    have he : Ω.ι ⁻¹' E i = r ⁻¹' (F i : Set (V i).toScheme) := by
      ext x
      change (∃ z ∈ (F i : Set (V i).toScheme), (V i).ι z = π i x.val) ↔ r x ∈ F i
      constructor
      · rintro ⟨z, hz, he⟩
        have hh : z = r x := Subtype.ext he
        rwa [← hh]
      · intro hx
        exact ⟨r x, hx, rfl⟩
    rw [he]
    exact (F i).isClosed.preimage hr
  have hclosure : ∀ i, Ω.ι ⁻¹' closure (E i) = Ω.ι ⁻¹' E i := by
    intro i
    rw [Ω.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage Ω.ι.continuous]
    exact (hclosed i).closure_eq
  have havoid : Disjoint (Ω : Set M) (⨆ i, K i).support := by
    apply Set.disjoint_left.mpr
    intro x hx hxK
    have hall : x ∈ ⋂ i, E i := by
      apply Set.mem_iInter.mpr
      intro i
      have hi : x ∈ closure (E i) := by
        exact (IdealSheafData.support_antitone (le_iSup K i)) hxK
      have hi' : (⟨x, hx⟩ : Ω.toScheme) ∈ Ω.ι ⁻¹' closure (E i) := hi
      rw [hclosure i] at hi'
      exact hi'
    rw [hempty] at hall
    exact hall
  have hdiff : ∀ i, E i ⊆ (K i).support \ (⨆ j, K j).support := by
    intro i x hx
    exact ⟨subset_closure hx, fun hh => Set.disjoint_left.mp havoid (hEΩ i hx) hh⟩
  refine ⟨Blowup.BlowupDatum.comap_eq_top_of_disjoint Ω havoid, ?_⟩
  let T : ι → Closeds B.Y := fun i =>
    Closeds.closure (B.map ⁻¹' ((K i).support \ (⨆ j, K j).support))
  refine ⟨T, Blowup.finite_boundary_separation K B, ?_⟩
  intro i x hx
  exact subset_closure (hdiff i hx)

end AlgebraicGeometry.Scheme.Compactification
