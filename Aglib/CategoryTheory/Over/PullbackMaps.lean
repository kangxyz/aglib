/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Original pullback maps, projection comparisons and actual Cartesian inverses -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.pullback

variable {C : Type*} [Category* C] {X S A B D : C}
  (p : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S)
  [HasPullback p a] [HasPullback p b]

/-- Change only the original right cospan arrow. -/
def mapRight (m : B ⟶ A) (hm : m ≫ a = b) : pullback p b ⟶ pullback p a :=
  pullback.lift (pullback.fst p b) (pullback.snd p b ≫ m)
    (by rw [Category.assoc, hm]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem mapRight_fst (m : B ⟶ A) (hm : m ≫ a = b) :
    mapRight p a b m hm ≫ pullback.fst p a = pullback.fst p b :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem mapRight_snd (m : B ⟶ A) (hm : m ≫ a = b) :
    mapRight p a b m hm ≫ pullback.snd p a = pullback.snd p b ≫ m :=
  pullback.lift_snd _ _ _

/-- The same actual cospan map with its original reversed-order target. -/
def mapRightToFlipped [HasPullback a p] (m : B ⟶ A) (hm : m ≫ a = b) :
    pullback p b ⟶ pullback a p :=
  pullback.lift (pullback.snd p b ≫ m) (pullback.fst p b)
    (by rw [Category.assoc, hm]; exact pullback.condition.symm)

omit [HasPullback p a] in
/-- Actual right-cospan composition retains the reversed-order target. -/
theorem mapRight_comp_toFlipped [HasPullback a p]
    (c : D ⟶ S) [HasPullback p c]
    (m : B ⟶ A) (hm : m ≫ a = b) (n : D ⟶ B) (hn : n ≫ b = c)
    (l : D ⟶ A) (hl : l ≫ a = c) (hcomp : n ≫ m = l) :
    mapRight p b c n hn ≫ mapRightToFlipped p a b m hm =
      mapRightToFlipped p a c l hl := by
  subst l
  apply pullback.hom_ext
  · simp only [Category.assoc, mapRightToFlipped, pullback.lift_fst, mapRight_snd_assoc]
  · simp only [Category.assoc, mapRightToFlipped, pullback.lift_snd, mapRight_fst]

/-- A map into a chosen pullback is the original Cartesian comparison when
its two projection equations agree with the specified square. -/
theorem map_eq_isoPullback_hom {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasPullback f g] {a : P ⟶ X} {b : P ⟶ Y} (h : IsPullback a b f g)
    (m : P ⟶ pullback f g) (hf : m ≫ pullback.fst f g = a)
    (hg : m ≫ pullback.snd f g = b) : m = h.isoPullback.hom :=
  pullback.hom_ext (hf.trans h.isoPullback_hom_fst.symm)
    (hg.trans h.isoPullback_hom_snd.symm)

/-- Pasting a Cartesian base square makes the actual fibre map invertible. -/
theorem isIso_map_of_isPullback {X S X' S' T : C}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (t : T ⟶ S')
    [HasPullback t f'] [HasPullback (t ≫ g) f] (H : IsPullback g' f' f g) :
    IsIso (pullback.map t f' (t ≫ g) f (𝟙 T) g' g (by simp) h) := by
  have H₀ : IsPullback (pullback.fst t f') (pullback.snd t f' ≫ g') (t ≫ g) f :=
    ((IsPullback.of_hasPullback t f').flip.paste_horiz H).flip
  have heq := map_eq_isoPullback_hom H₀
    (pullback.map t f' (t ≫ g) f (𝟙 T) g' g (by simp) h)
    (by simp only [pullback.map, pullback.lift_fst, Category.comp_id])
    (by simp only [pullback.map, pullback.lift_snd])
  rw [heq]
  infer_instance

/-- Actual isomorphism coordinates determine the original pullback-map square. -/
theorem map_iso_square {X S A B P Q : C} (f : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S)
    [HasPullback a f] [HasPullback b f]
    (e : P ≅ pullback a f) (d : Q ≅ pullback b f)
    (μ : pullback b f ⟶ pullback a f) (l : Q ⟶ P) (r : B ⟶ A)
    (s : P ⟶ A) (t : Q ⟶ B) (x : P ⟶ X) (y : Q ⟶ X)
    (ef : e.hom ≫ pullback.fst a f = s) (es : e.hom ≫ pullback.snd a f = x)
    (df : d.hom ≫ pullback.fst b f = t) (ds : d.hom ≫ pullback.snd b f = y)
    (mf : μ ≫ pullback.fst a f = pullback.fst b f ≫ r)
    (ms : μ ≫ pullback.snd a f = pullback.snd b f)
    (lf : l ≫ s = t ≫ r) (ls : l ≫ x = y) : d.hom ≫ μ = l ≫ e.hom := by
  apply pullback.hom_ext
  · calc
      _ = d.hom ≫ (μ ≫ pullback.fst a f) := Category.assoc _ _ _
      _ = d.hom ≫ (pullback.fst b f ≫ r) := congrArg (fun k => d.hom ≫ k) mf
      _ = (d.hom ≫ pullback.fst b f) ≫ r := (Category.assoc _ _ _).symm
      _ = t ≫ r := congrArg (fun k => k ≫ r) df
      _ = l ≫ s := lf.symm
      _ = l ≫ (e.hom ≫ pullback.fst a f) := congrArg (fun k => l ≫ k) ef.symm
      _ = _ := (Category.assoc _ _ _).symm
  · calc
      _ = d.hom ≫ (μ ≫ pullback.snd a f) := Category.assoc _ _ _
      _ = d.hom ≫ pullback.snd b f := congrArg (fun k => d.hom ≫ k) ms
      _ = y := ds
      _ = l ≫ x := ls.symm
      _ = l ≫ (e.hom ≫ pullback.snd a f) := congrArg (fun k => l ≫ k) es.symm
      _ = _ := (Category.assoc _ _ _).symm

theorem isPullback_of_projection_iso {C : Type*} [Category* C]
    {X Y Z W : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (e : W ≅ pullback f g) (p : W ⟶ X) (q : W ⟶ Y)
    (hp : e.hom ≫ pullback.fst f g = p) (hq : e.hom ≫ pullback.snd f g = q) :
    IsPullback p q f g := by
  have hw : p ≫ f = q ≫ g := by
    calc
      _ = (e.hom ≫ pullback.fst f g) ≫ f := congrArg (fun k => k ≫ f) hp.symm
      _ = e.hom ≫ (pullback.fst f g ≫ f) := Category.assoc _ _ _
      _ = e.hom ≫ (pullback.snd f g ≫ g) :=
        congrArg (fun k => e.hom ≫ k) (pullback.condition (f := f) (g := g))
      _ = (e.hom ≫ pullback.snd f g) ≫ g := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun k => k ≫ g) hq
  exact IsPullback.of_iso_pullback ⟨hw⟩ e hp hq


end CategoryTheory.Limits.pullback
