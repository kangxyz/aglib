/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.NatIso

/-!
# Naturality and factors through actual comparison maps

Naturality and the supplied original chart conjugacy give the whole original
coefficient square. Lifts through the actual comparison isomorphisms retain
the same original arrow and the same local factor.
-/

@[expose] public section

open CategoryTheory Opposite
namespace CategoryTheory.Functor.NaturalityTransport
universe u v

theorem functor_square_apply {C : Type v} [Category.{u} C] (F : C ⥤ FintypeCat.{u})
    {A A' B B' : C} (i : A ⟶ A') (j : B ⟶ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : i ≫ g = f ≫ j) (x : F.obj A) :
    F.map j (F.map f x) = F.map g (F.map i x) := by
  have he := congrArg F.map h
  rw [Functor.map_comp, Functor.map_comp] at he
  exact (ConcreteCategory.congr_hom he x).symm

theorem naturality_via_injective {A A' B B' : Type u}
    (i : A → A') (j : B → B') (hj : Function.Injective j) (f : A → B) (g : A' → B')
    (a : A → A) (a' : A' → A') (b : B → B) (b' : B' → B')
    (hsq : ∀ x, j (f x) = g (i x)) (hi : ∀ x, i (a x) = a' (i x))
    (hja : ∀ y, j (b y) = b' (j y)) (hg : ∀ x, g (a' x) = b' (g x)) (x : A) :
    f (a x) = b (f x) := by
  apply hj
  calc
    j (f (a x)) = g (i (a x)) := hsq _
    _ = g (a' (i x)) := congrArg g (hi x)
    _ = b' (g (i x)) := hg _
    _ = b' (j (f x)) := congrArg b' (hsq x).symm
    _ = j (b (f x)) := (hja _).symm

/-- Original relative-object naturality transports through the two supplied
original chart isomorphisms, using their original conjugacy equation. -/
theorem contraFunctorIso_chart_naturality
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (P : Aᵒᵖ ⥤ C) (Q : Bᵒᵖ ⥤ D) (R : A ⥤ B) (L : C ⥤ D)
    (e : P ⋙ L ≅ R.op ⋙ Q) {Y Z : A} (h : Y ⟶ Z)
    {Y' Z' : B} (a : Y' ≅ R.obj Y) (b : Z' ≅ R.obj Z) (r : Y' ⟶ Z')
    (hc : a.hom ≫ R.map h = r ≫ b.hom) :
    L.map (P.map h.op) ≫ (e.hom.app (op Y) ≫ Q.map a.hom.op) =
      (e.hom.app (op Z) ≫ Q.map b.hom.op) ≫ Q.map r.op := by
  have he : L.map (P.map h.op) ≫ e.hom.app (op Y) =
      e.hom.app (op Z) ≫ Q.map (R.map h).op := e.hom.naturality h.op
  have hm : Q.map (R.map h).op ≫ Q.map a.hom.op =
      Q.map b.hom.op ≫ Q.map r.op :=
    (Q.map_comp (R.map h).op a.hom.op).symm.trans
      ((congrArg (fun k => Q.map k.op) hc).trans (Q.map_comp b.hom.op r.op))
  exact (Category.assoc (L.map (P.map h.op)) (e.hom.app (op Y))
    (Q.map a.hom.op)).symm.trans
      ((congrArg (fun k => k ≫ Q.map a.hom.op) he).trans
        ((Category.assoc (e.hom.app (op Z)) (Q.map (R.map h).op)
          (Q.map a.hom.op)).trans
            ((congrArg (fun k => e.hom.app (op Z) ≫ k) hm).trans
              (Category.assoc (e.hom.app (op Z)) (Q.map b.hom.op) (Q.map r.op)).symm)))

/-- A lift in the actual supplied iso square gives a lift through the
original arrow, preserving that same original coefficient map. -/
theorem factor_through_original_iso_square
    {C : Type*} [Category* C] {A B A' B' F : C}
    (eA : A ≅ A') (eB : B ≅ B') (τ : B ⟶ A) (τ' : B' ⟶ A')
    (hτ : τ ≫ eA.hom = eB.hom ≫ τ')
    (α : F ⟶ A) (β : F ⟶ B') (hβ : β ≫ τ' = α ≫ eA.hom) :
    (β ≫ eB.inv) ≫ τ = α := by
  apply (cancel_mono eA.hom).mp
  simp only [Category.assoc, hτ, Iso.inv_hom_id_assoc, hβ]


end CategoryTheory.Functor.NaturalityTransport

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 467dcb06deb3bfa1a3fed825c29e664ac0ee442b5ff11681cfae7082b9f3ac1f.
Definitions, hypotheses and universes are retained modulo native names. -/
