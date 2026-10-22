/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Finite subsets of filtered colimits

Every finite subset of a specified filtered colimit of types is contained in
the image of one original stage. No injectivity or surjectivity condition on
transition maps is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.Types

universe u v w

/-- A finite subset of a filtered colimit lies in the image of one stage. -/
theorem exists_finset_subset_range_of_isColimit
    {I : Type v} [Category.{w} I] [IsFiltered I]
    (D : I ⥤ Type u) (c : Cocone D) (hc : IsColimit c) (s : Finset c.pt) :
    ∃ i, (s : Set c.pt) ⊆ Set.range (c.ι.app i) := by
  classical
  choose j a ha using fun x : s ↦ jointly_surjective_of_isColimit hc x.1
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let q (x : s) : j x ⟶ k := (hk (Finset.mem_image_of_mem j (Finset.mem_univ x))).some
  refine ⟨k, fun x hx ↦ ⟨D.map (q ⟨x, hx⟩) (a ⟨x, hx⟩), ?_⟩⟩
  exact (ConcreteCategory.congr_hom (c.w (q ⟨x, hx⟩)) (a ⟨x, hx⟩)).trans (ha ⟨x, hx⟩)

end CategoryTheory.Limits.Types
