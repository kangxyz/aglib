/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Original pullback comparison obtained by Cartesian pasting

Pulling an arbitrary arrow back through the top map of an actual Cartesian
square agrees with pulling its original structural composite back through
the bottom map. Both directions retain their original projections.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.IsPullback

universe v u

variable {C : Type u} [Category.{v} C]
    {A B D S W : C} {b : A ⟶ B} {p : A ⟶ D} {f : B ⟶ S} {g : D ⟶ S}
    (H : IsPullback b p f g) (q : W ⟶ B)
    [HasPullback q b] [HasPullback g (q ≫ f)]

/-- The canonical comparison for the two original ways to form this base change. -/
def familyPullbackIso : pullback q b ≅ pullback g (q ≫ f) :=
  ((IsPullback.of_hasPullback q b).flip.paste_horiz H.flip).isoPullback

@[reassoc (attr := simp)]
theorem familyPullbackIso_hom_fst :
    (familyPullbackIso H q).hom ≫ pullback.fst g (q ≫ f) =
      pullback.snd q b ≫ p :=
  ((IsPullback.of_hasPullback q b).flip.paste_horiz H.flip).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem familyPullbackIso_hom_snd :
    (familyPullbackIso H q).hom ≫ pullback.snd g (q ≫ f) = pullback.fst q b :=
  ((IsPullback.of_hasPullback q b).flip.paste_horiz H.flip).isoPullback_hom_snd

@[reassoc (attr := simp)]
theorem familyPullbackIso_inv_fst :
    (familyPullbackIso H q).inv ≫ pullback.snd q b ≫ p =
      pullback.fst g (q ≫ f) := by
  simpa only [familyPullbackIso, Category.assoc] using
    ((IsPullback.of_hasPullback q b).flip.paste_horiz H.flip).isoPullback_inv_fst

@[reassoc (attr := simp)]
theorem familyPullbackIso_inv_snd :
    (familyPullbackIso H q).inv ≫ pullback.fst q b = pullback.snd g (q ≫ f) :=
  ((IsPullback.of_hasPullback q b).flip.paste_horiz H.flip).isoPullback_inv_snd

end CategoryTheory.IsPullback
