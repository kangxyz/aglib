/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Invertibility from original mate and component equations

The given mate component and the target unit determine invertibility of the
image of the original source unit. Only the stated components are assumed
invertible. The source unit, the adjunctions and Mathlib's mate are unchanged.

The component equation also reflects invertibility of a supplied original
arrow through a conservative functor, using its actual invertible comparison
arrows. This calculation is performed before concrete functor specialization.
-/

@[expose] public noncomputable section

namespace CategoryTheory

/-- The native unit/mate equation reflects the stated component invertibility
back to the image of the original unit, without an equality-cancellation claim. -/
theorem isIso_map_unit_of_iso_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : A ⥤ C} {H : B ⥤ D}
    (α : G ⋙ L' ≅ L ⋙ H) (β : R ⋙ G ⟶ H ⋙ R')
    (hβ : β = (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.hom)).natTrans)
    (M : A) (hβM : IsIso (β.app (L.obj M)))
    (hunit : IsIso (adj'.unit.app (G.obj M))) : IsIso (G.map (adj.unit.app M)) := by
  subst β
  change IsIso ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.hom)).app (L.obj M)) at hβM
  have : IsIso (G.map (adj.unit.app M) ≫
      (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.hom)).app (L.obj M)) := by
    rw [unit_mateEquiv]
    change IsIso (adj'.unit.app (G.obj M) ≫ R'.map (α.hom.app M))
    infer_instance
  exact IsIso.of_isIso_comp_right (G.map (adj.unit.app M))
    ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.hom)).app (L.obj M))

/-- A proved component equation with invertible comparison arrows reflects
invertibility of the supplied original arrow through a conservative functor. -/
theorem isIso_of_component_equation
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {M N : C} {P A B Q : D} (β : M ⟶ N) {a : A ⟶ B}
    (u : P ⟶ A) (v : B ⟶ Q) (s : P ⟶ F.obj M) (t : F.obj N ⟶ Q)
    (h : u ≫ a ≫ v = s ≫ F.map β ≫ t)
    (ha : IsIso a) (hu : IsIso u) (hv : IsIso v)
    (hs : IsIso s) (ht : IsIso t) (hF : F.ReflectsIsomorphisms) : IsIso β := by
  let : IsIso a := ha
  let : IsIso u := hu
  let : IsIso v := hv
  let : IsIso s := hs
  let : IsIso t := ht
  let : F.ReflectsIsomorphisms := hF
  have hc : IsIso (s ≫ F.map β ≫ t) := by
    rw [← h]
    infer_instance
  have hr : IsIso (F.map β ≫ t) := (isIso_comp_left_iff s _).mp hc
  have : IsIso (F.map β) := (isIso_comp_right_iff _ t).mp hr
  exact isIso_of_reflects_iso β F

end CategoryTheory
