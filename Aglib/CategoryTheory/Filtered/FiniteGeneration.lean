/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-! # Finite generation detected by finitely many compact images

A finite jointly faithful family detects an epimorphic leg of an original
filtered colimit whenever it preserves that colimit and its apex images are
finitely presentable. Identity factorization gives split epimorphic legs in
each target. One common later stage is then epimorphic in the original category.
No abelian, exactness, or preservation-of-all-colimits hypothesis is needed.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe uC vC uK uE vE w

/-- A finite jointly faithful family with compact apex images detects an
actual epimorphic leg of the original filtered colimit cocone. -/
theorem JointlyFaithful.exists_epi_of_isColimit
    {C : Type uC} [Category.{vC} C]
    {K : Type uK} [Finite K] {E : K → Type uE} [∀ k, Category.{vE} (E k)]
    (L : ∀ k, C ⥤ E k) (hL : JointlyFaithful L)
    {I : Type w} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ C} {c : Cocone D} (hc : IsColimit c)
    [∀ k, PreservesColimit D (L k)]
    [∀ k, IsFinitelyPresentable.{w} ((L k).obj c.pt)] :
    ∃ i, Epi (c.ι.app i) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hfactor (k : K) : ∃ i, ∃ a : (L k).obj c.pt ⟶ (L k).obj (D.obj i),
      a ≫ (L k).map (c.ι.app i) = 𝟙 _ :=
    IsFinitelyPresentable.exists_hom_of_isColimit (X := (L k).obj c.pt)
      (isColimitOfPreserves (L k) hc) (𝟙 ((L k).obj c.pt))
  choose i a ha using hfactor
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  have hmap (k : K) : Epi ((L k).map (c.ι.app j)) := by
    let b : i k ⟶ j := (hj (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)).some
    apply epi_of_epi_fac (f := a k ≫ (L k).map (D.map b)) (h := 𝟙 _)
    rw [Category.assoc, ← (L k).map_comp, c.w b]
    exact ha k
  exact ⟨j, hL.jointlyReflectEpimorphisms.epi (c.ι.app j)⟩

end CategoryTheory
