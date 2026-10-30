/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Basic

/-! # Coefficient squares on the original functor values

The same indexed family supplies both transport values. A functor then
assembles the two original composition equations and coefficient-naturality
equations through the actual ordinary coefficient square. All calculations
precede specialization to a concrete cohomology functor or value.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe uC vC e uI

/-- Assemble the complete square from original composition and naturality
values. Equality transport is proved from the same indexed value family;
no equality of complete routes is required as a premise. -/
theorem map_coefficient_square_of_family_values
    {C : Type uC} [Category.{vC} C] (T : C ⥤ AddCommGrpCat.{e})
    {I : Type uI} (K : I → C) (z : ∀ i, T.obj (K i)) {i j : I} (h : i = j)
    {A B A' B' D : C}
    (c : K i ⟶ A) (d : K j ⟶ A')
    (α : A ⟶ B) (β : B ⟶ D) (γ : A' ⟶ B') (δ : B' ⟶ D)
    (hc : c ≫ α ≫ β = (eqToIso (congrArg K h)).hom ≫ d ≫ γ ≫ δ)
    {xL : T.obj A} {xR : T.obj A'} {yL : T.obj B} {yR : T.obj B'}
    (hcompL : T.map c (z i) = xL) (hcompR : T.map d (z j) = xR)
    (hnatL : yL = T.map α xL) (hnatR : yR = T.map γ xR) :
    T.map β yL = T.map δ yR := by
  cases h
  rw [hnatL, hnatR, ← hcompL, ← hcompR]
  have hh := congrArg (fun q : K i ⟶ D => T.map q (z i)) hc
  simpa only [eqToIso.hom, eqToHom_refl, Category.id_comp, Functor.map_comp,
    CategoryTheory.comp_apply] using hh

end CategoryTheory.Functor
