/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.LargeColimits
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.GroupTheory.Torsion

/-!
# Internal torsion and original point fibres

The local annihilator condition implies torsion of every original abelian
point fibre. A small conservative family of points also detects the local
condition. Both implications use the original colimit germs and actual
covering sieves, with no sectionwise global-annihilator assertion.
-/

@[expose] public noncomputable section

open Opposite

namespace CategoryTheory.Presheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [LocallySmall.{w} C] {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}}

/-- Local annihilators make every original point fibre a torsion abelian group. -/
theorem IsLocallyTorsion.isAddTorsion_fiber (hF : IsLocallyTorsion J F)
    (Φ : GrothendieckTopology.Point.{w} J) :
    IsAddTorsion ((Φ.presheafFiber (A := AddCommGrpCat.{w})).obj F) := by
  intro z
  obtain ⟨U, x, s, rfl⟩ := Φ.toPresheafFiber_jointly_surjective z
  obtain ⟨V, f, ⟨n, hn, hs⟩, y, hy⟩ := Φ.jointly_surjective _ (hF U s) x
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨n, hn, ?_⟩
  rw [← hy, ← Φ.toPresheafFiber_w_apply f y F s, ← map_nsmul, hs, map_zero]

/-- Torsion of the original fibres in a small conservative family detects internal torsion. -/
theorem isLocallyTorsion_of_isAddTorsion_fibers
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    (P : ObjectProperty (GrothendieckTopology.Point.{w} J))
    [ObjectProperty.Small.{w} P] (hP : P.IsConservativeFamilyOfPoints)
    (hF : ∀ Φ : P.FullSubcategory,
      IsAddTorsion ((Φ.obj.presheafFiber (A := AddCommGrpCat.{w})).obj F)) :
    IsLocallyTorsion J F := by
  intro U s
  let R := torsionSieve F s
  change R ∈ J U
  rw [← Sieve.ofArrows_category R, hP.jointly_reflect_ofArrows_mem_of_small]
  intro Φ x
  obtain ⟨n, hn, hs⟩ := (hF Φ (Φ.obj.toPresheafFiber U x F s)).exists_nsmul_eq_zero
  have heq : Φ.obj.toPresheafFiber U x F (n • s) =
      Φ.obj.toPresheafFiber U x F 0 := by
    simpa only [map_nsmul, map_zero] using hs
  obtain ⟨V, f, y, hy, hf⟩ :=
    (Φ.obj.toPresheafFiber_eq_iff' U x (n • s) 0).mp heq
  have hr : R f := ⟨n, hn, by simpa only [map_nsmul, map_zero] using hf⟩
  exact ⟨⟨Over.mk f, hr⟩, y, hy⟩

/-- The local definition equals torsion in every original fibre of the chosen family. -/
theorem isLocallyTorsion_iff_isAddTorsion_fibers
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    (P : ObjectProperty (GrothendieckTopology.Point.{w} J))
    [ObjectProperty.Small.{w} P] (hP : P.IsConservativeFamilyOfPoints) :
    IsLocallyTorsion J F ↔
      ∀ Φ : P.FullSubcategory,
        IsAddTorsion ((Φ.obj.presheafFiber (A := AddCommGrpCat.{w})).obj F) :=
  ⟨fun h Φ => h.isAddTorsion_fiber Φ.obj,
    isLocallyTorsion_of_isAddTorsion_fibers P hP⟩

end CategoryTheory.Presheaf
