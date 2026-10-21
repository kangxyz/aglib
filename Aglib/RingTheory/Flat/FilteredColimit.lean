/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Flatness over a filtered colimit of rings

A module over an actual filtered ring colimit is flat if its restriction along
every cocone map is flat. Only the finite tuple of coefficients of a relation
is moved to a common stage; the module and its elements remain unchanged.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace Module.Flat

variable {J : Type v} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{max u v}) {c : Cocone F} (hc : IsColimit c)

include hc

/-- A finite tuple of colimit elements has representatives in a common stage. -/
private lemma exists_fin_rep {n : ℕ} (x : Fin n → c.pt) :
    ∃ (j : J) (a : Fin n → F.obj j), ∀ i, c.ι.app j (a i) = x i := by
  classical
  let : PreservesFilteredColimitsOfSize.{v, v} (forget CommRingCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink (forget CommRingCat.{max u v})
  choose j a ha using fun i => Concrete.isColimit_exists_rep F hc (x i)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let f : ∀ i, j i ⟶ k := fun i =>
    Classical.choice (hk (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  refine ⟨k, fun i => F.map (f i) (a i), fun i => ?_⟩
  rw [← ConcreteCategory.comp_apply, c.w]
  exact ha i

/-- A module over a filtered colimit of commutative rings is flat if its
restriction along every actual cocone map is flat. The restricted actions
are fixed by `Module.compHom`, not independently chosen module structures. -/
lemma of_isColimit (M : Type w) [AddCommGroup M] [Module c.pt M]
    (hflat : ∀ j, letI : Module (F.obj j) M :=
        Module.compHom M (show F.obj j →+* c.pt from (c.ι.app j).hom);
      Module.Flat (F.obj j) M) : Module.Flat c.pt M := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro n r x hr
  obtain ⟨j, a, ha⟩ := exists_fin_rep F hc r
  let φ : F.obj j →+* c.pt := (c.ι.app j).hom
  let : Module (F.obj j) M := Module.compHom M φ
  have : Module.Flat (F.obj j) M := hflat j
  have hstage : ∑ i, a i • x i = 0 := by
    change ∑ i, φ (a i) • x i = 0
    simpa only [φ, ha] using hr
  obtain ⟨k, b, y, hb, hab⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hstage
  refine ⟨k, fun i t => φ (b i t), y, fun i => ?_, fun t => ?_⟩
  · exact hb i
  · calc
      ∑ i, r i * φ (b i t) = ∑ i, φ (a i * b i t) := by
        simp only [map_mul, φ, ha]
      _ = φ (∑ i, a i * b i t) := (map_sum φ _ _).symm
      _ = 0 := by rw [hab t, map_zero]

end Module.Flat
