/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Finite families of sections at a common inverse-limit stage

Specified global sections of a qcqs affine-transition limit lift simultaneously
to one stage. If their basic opens cover the limit, a later family still lifts
the same original sections and already covers that stage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u v

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u})
  [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  (c : Cone D) (hc : IsLimit c)

include hc in
/-- A finite family of original global sections lifts to one common stage. -/
theorem exists_finite_sections_at_stage {J : Type v} [Finite J]
    (r : J → Γ(c.pt, ⊤)) :
    ∃ (i : I) (t : J → Γ(D.obj i, ⊤)), ∀ j, (c.π.app i).appTop (t j) = r j := by
  classical
  let : Fintype J := Fintype.ofFinite J
  choose k t ht using fun j ↦ AlgebraicGeometry.exists_appTop_π_eq_of_isLimit D c hc (r j)
  obtain ⟨i, fi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  let f (j : J) : i ⟶ k j := (fi (by simp)).some
  refine ⟨i, fun j ↦ (D.map (f j)).appTop (t j), fun j ↦ ?_⟩
  rw [← CommRingCat.comp_apply, ← Hom.comp_appTop, c.w]
  exact (ht j).symm

include hc in
/-- A specified finite basic-open cover of the limit lifts, with its sections,
to a basic-open cover at an actual stage. -/
theorem exists_finite_basicOpen_cover_at_stage {J : Type v} [Finite J]
    (r : J → Γ(c.pt, ⊤)) (hr : (⨆ j, c.pt.basicOpen (r j)) = ⊤) :
    ∃ (i : I) (t : J → Γ(D.obj i, ⊤)),
      (∀ j, (c.π.app i).appTop (t j) = r j) ∧ (⨆ j, (D.obj i).basicOpen (t j)) = ⊤ := by
  obtain ⟨i, t, ht⟩ := exists_finite_sections_at_stage D c hc r
  have hU : c.π.app i ⁻¹ᵁ (⨆ j, (D.obj i).basicOpen (t j)) = ⊤ := by
    rw [Hom.preimage_iSup]
    simp only [Scheme.preimage_basicOpen_top]
    change (⨆ j, c.pt.basicOpen ((c.π.app i).appTop (t j))) = ⊤
    simpa only [ht] using hr
  obtain ⟨k, g, hg⟩ := AlgebraicGeometry.exists_map_eq_top D c hc _ hU
  refine ⟨k, fun j ↦ (D.map g).appTop (t j), ?_, ?_⟩
  · intro j
    rw [← CommRingCat.comp_apply, ← Hom.comp_appTop, c.w]
    exact ht j
  · simpa only [Hom.preimage_iSup, Scheme.preimage_basicOpen_top] using hg

end AlgebraicGeometry.Scheme
