/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.SequentialSystem.SignCorrection

/-! Arbitrary morphisms retain their literal alternating components. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits.SequentialSystem

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

example {F G : ℕ ⥤ C} (a : ∀ n, F.obj n ⟶ G.obj n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ a (n + 1) =
      -(a n ≫ G.map (homOfLE (Nat.le_succ n)))) (n : ℕ) :
    (signCorrectionHom a h).app n = (-1 : ℤ) ^ n • a n :=
  signCorrectionHom_app a h n

example {F G : ℕ ⥤ C} (a : ∀ n, F.obj n ⟶ G.obj n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ a (n + 1) =
      -(a n ≫ G.map (homOfLE (Nat.le_succ n)))) :
    (signCorrectionHom a h).app 0 = a 0 := by simp

example {F G : ℕ ⥤ C} (a : ∀ n, F.obj n ⟶ G.obj n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ a (n + 1) =
      -(a n ≫ G.map (homOfLE (Nat.le_succ n)))) {m n : ℕ} (f : m ⟶ n) :
    F.map f ≫ (signCorrectionHom a h).app n =
      (signCorrectionHom a h).app m ≫ G.map f :=
  (signCorrectionHom a h).naturality f

example {F G : ℕ ⥤ C} (e : ∀ n, F.obj n ≅ G.obj n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ (e (n + 1)).hom =
      -((e n).hom ≫ G.map (homOfLE (Nat.le_succ n)))) :
    signCorrectionHom (fun n ↦ (e n).hom) h = (signCorrectionIso e h).hom :=
  signCorrectionHom_eq_iso_hom e h

example {X Y : C} (n : ℕ) (e : X ≅ Y) :
    (alternatingIso n e).hom = (-1 : ℤ) ^ n • e.hom :=
  alternatingIso_hom n e
