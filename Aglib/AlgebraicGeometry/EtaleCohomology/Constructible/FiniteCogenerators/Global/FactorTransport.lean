/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.NatIso
public import Aglib.CategoryTheory.Functor.NaturalityTransport

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
  exact CategoryTheory.Functor.NaturalityTransport.contraFunctorIso_chart_naturality
    P Q R L e h a b r hc

/-- A lift in the actual supplied iso square gives a lift through the
original arrow, preserving that same original coefficient map. -/
theorem factor_through_original_iso_square
    {C : Type*} [Category* C] {A B A' B' F : C}
    (eA : A ≅ A') (eB : B ≅ B') (τ : B ⟶ A) (τ' : B' ⟶ A')
    (hτ : τ ≫ eA.hom = eB.hom ≫ τ')
    (α : F ⟶ A) (β : F ⟶ B') (hβ : β ≫ τ' = α ≫ eA.hom) :
    (β ≫ eB.inv) ≫ τ = α := by
  exact CategoryTheory.Functor.NaturalityTransport.factor_through_original_iso_square
    eA eB τ τ' hτ α β hβ

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
