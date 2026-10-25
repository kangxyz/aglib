/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.NatIso

/-! # Original coefficient factorization through the original chart isomorphisms

A relative-object natural isomorphism and the original chart-map conjugacy
give the full original coefficient square. A local lift through that square
then lifts through the original arrow. The argument stays at abstract whole
objects and maps before any concrete generated algebra is substituted.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

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

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
