/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.OpenImmersion

/-!
# Separated open gluing after modifying one model

A closed overlap graph remains closed when its right-hand map is lifted through
a separated modification. The proof cancels the separated comparison of the
actual products. It does not identify the entire inverse image of the old graph
with the new overlap, which is generally false.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.SeparatedGluing

set_option backward.isDefEq.respectTransparency false in
/-- A lifted overlap graph is closed if its composite graph is closed and the
modification on the right is separated. -/
theorem isClosedImmersion_overlapGraph_of_separated
    {W T Yn Y S : Scheme.{u}} (j : W ⟶ T) (r : W ⟶ Yn)
    (δ : Yn ⟶ Y) [IsSeparated δ] (pT : T ⟶ S) (pY : Y ⟶ S)
    (hc : j ≫ pT = (r ≫ δ) ≫ pY)
    [IsClosedImmersion (pullback.lift j (r ≫ δ) hc)] :
    IsClosedImmersion (pullback.lift j r (hc.trans (Category.assoc r δ pY))) := by
  let m := pullback.map pT (δ ≫ pY) pT pY (𝟙 T) δ (𝟙 S)
    (by simp) (by simp)
  let : IsSeparated m := MorphismProperty.pullbackMap
    (P := @IsSeparated.{u}) (inferInstance : IsSeparated (𝟙 T))
    (inferInstance : IsSeparated δ) (by simp) rfl
  have hm : pullback.lift j r (hc.trans (Category.assoc r δ pY)) ≫ m =
      pullback.lift j (r ≫ δ) hc := by
    apply pullback.hom_ext <;>
      simp only [m, pullback.map, Category.assoc, pullback.lift_fst,
        pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  let : IsClosedImmersion
      (pullback.lift j r (hc.trans (Category.assoc r δ pY)) ≫ m) := by
    rw [hm]
    infer_instance
  exact IsClosedImmersion.of_comp _ m

/-- The actual open pushout of the modified models is separated over the base.
Its structure morphism is the native descent map, retaining both chart triangles. -/
theorem separated_desc_of_closed_composite_graph
    {W T Yn Y S : Scheme.{u}} (j : W ⟶ T) (r : W ⟶ Yn)
    [IsOpenImmersion j] [IsOpenImmersion r]
    (δ : Yn ⟶ Y) [IsSeparated δ] (pT : T ⟶ S) (pY : Y ⟶ S)
    [IsSeparated pT] [IsSeparated pY]
    (hc : j ≫ pT = (r ≫ δ) ≫ pY)
    [IsClosedImmersion (pullback.lift j (r ≫ δ) hc)] :
    IsSeparated (pushout.desc pT (δ ≫ pY) (hc.trans (Category.assoc r δ pY))) := by
  let : IsClosedImmersion (pullback.lift j r (hc.trans (Category.assoc r δ pY))) :=
    isClosedImmersion_overlapGraph_of_separated j r δ pT pY hc
  exact separated_desc j r pT (δ ≫ pY) (hc.trans (Category.assoc r δ pY))

end AlgebraicGeometry.Scheme.SeparatedGluing
