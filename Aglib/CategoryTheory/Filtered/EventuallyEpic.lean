/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Filtered.FiniteGeneration

/-! # A common epimorphic stage detected by a finite family

For the original filtered cocone, eventual epimorphy after each of finitely
many jointly faithful functors gives an epimorphic original leg. The result
needs no preservation of colimits or epimorphisms, and no compactness premise.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe uC vC uK uE vE w

/-- Finitely many eventual epimorphic images of the same filtered cocone
have a common epimorphic stage in the original category. -/
theorem JointlyFaithful.exists_epi_of_eventually_epi
    {C : Type uC} [Category.{vC} C]
    {K : Type uK} [Finite K] {E : K → Type uE} [∀ k, Category.{vE} (E k)]
    (L : ∀ k, C ⥤ E k) (hL : JointlyFaithful L)
    {I : Type w} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ C} (c : Cocone D)
    (h : ∀ k, ∃ i, Epi ((L k).map (c.ι.app i))) : ∃ i, Epi (c.ι.app i) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  choose i hi using h
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  have (k : K) : Epi ((L k).map (c.ι.app j)) := by
    let b : i k ⟶ j := (hj (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)).some
    let : Epi ((L k).map (c.ι.app (i k))) := hi k
    apply epi_of_epi_fac (f := (L k).map (D.map b))
      (h := (L k).map (c.ι.app (i k)))
    rw [← (L k).map_comp, c.w b]
  exact ⟨j, hL.jointlyReflectEpimorphisms.epi (c.ι.app j)⟩

end CategoryTheory
