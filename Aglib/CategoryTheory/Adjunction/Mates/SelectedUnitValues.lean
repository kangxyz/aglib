/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.LeftAdjointComparison

/-! # Original unit and counit values of selected left-adjoint comparisons

The native uniqueness comparison is retained literally. These component views
normalize the original adjunction laws before concrete coefficient categories
are substituted; they choose no replacement adjunction or comparison.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.SelectedAdjointUnit

/-- The original comparison preserves the actual source unit and right comparison. -/
theorem unit_app
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (e : R ≅ R') (X : C) :
    a.unit.app X ≫ R.map (((a.ofNatIsoRight e).leftAdjointUniq b).hom.app X) ≫
        e.hom.app (L'.obj X) = b.unit.app X := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (a.ofNatIsoRight e) b X
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  simpa only [Adjunction.homEquiv_unit, Functor.comp_obj, Category.assoc] using h

/-- The original identity comparison retains the actual counit. -/
theorem identity_counit_app
    {C : Type*} [Category* C] {L R : C ⥤ C}
    (a : L ⊣ R) (e : R ≅ 𝟭 C) (X : C) :
    a.counit.app X =
      ((a.ofNatIsoRight e).leftAdjointUniq Adjunction.id).hom.app (R.obj X) ≫
        e.hom.app X := by
  let c := (a.ofNatIsoRight e).leftAdjointUniq Adjunction.id
  have hc := conjugateEquiv_counit Adjunction.id a c.hom X
  have he : conjugateEquiv Adjunction.id a c.hom = e.inv :=
    conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom a Adjunction.id e
  rw [he] at hc
  change L.map (e.inv.app X) ≫ a.counit.app X = c.hom.app X ≫ 𝟙 X at hc
  have hn := c.hom.naturality (e.inv.app X)
  apply (cancel_epi (L.map (e.inv.app X))).1
  rw [hc, ← Category.assoc, hn]
  simp only [Functor.id_map, Functor.id_obj, Category.assoc, Iso.inv_hom_id_app]

end CategoryTheory.SelectedAdjointUnit
