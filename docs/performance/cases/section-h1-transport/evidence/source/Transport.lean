/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.SourceSection

/-! # Original section comparison through equality transport

The whole comparison and its original objectwise component use the same
functor family and indexing equality. The value equality is proved before
any concrete category, cohomology class or coefficient map is supplied.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe uI uC vC uD vD

/-- The whole original section comparison has its equality-transported component. -/
theorem sourceSectionIso_transport_app
    {I : Type uI} {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {F : C ⥤ D} {G : D ⥤ C}
    (K : I → C ⥤ C) {i j : I} (h : i = j)
    (c : K i ≅ F ⋙ G) (e : K j ≅ 𝟭 C) (L : C) :
    (sourceSectionIso c (eqToIso (congrArg K h) ≪≫ e)).app L =
      (c.app L).symm ≪≫
        eqToIso (congrArg (fun k => (K k).obj L) h) ≪≫ e.app L := by
  cases h
  rfl


universe eC eV eW

/-- Evaluate inverse composition and two original transports while retaining
both the complete function and its actual input/output values. -/
theorem map_inverse_transport_apply_of_values
    {C : Type uC} [Category.{vC} C] (T : C ⥤ AddCommGrpCat.{eC})
    {A B D L : C} (c : A ≅ B) (t : A ≅ D) (e : D ≅ L)
    (φ : B ⟶ L) (hφ : φ = c.inv ≫ t.hom ≫ e.hom)
    {V : Type eV} (E : V → T.obj L) (P : V → T.obj B)
    (hE : E = fun b => T.map φ (P b))
    (b : V) (x : T.obj A) (y : T.obj D) (a : T.obj L)
    (hc : T.map c.hom x = P b) (ht : T.map t.hom x = y)
    (he : T.map e.hom y = a) : E b = a := by
  rw [hE, hφ, Functor.map_comp, Functor.map_comp]
  change T.map e.hom (T.map t.hom (T.map c.inv (P b))) = a
  rw [← hc]
  have hi : T.map c.inv (T.map c.hom x) = x :=
    ConcreteCategory.congr_hom (T.mapIso c).hom_inv_id x
  rw [hi, ht, he]

/-- An original coefficient square and original pullback equation give the
same complete function square, with independent input and output worlds. -/
theorem map_coefficient_square_apply_of_values
    {C : Type uC} [Category.{vC} C] (T : C ⥤ AddCommGrpCat.{eC})
    {A B L M : C} (r : A ⟶ B) (q : L ⟶ M)
    (φ : A ⟶ L) (ψ : B ⟶ M) (hs : r ≫ ψ = φ ≫ q)
    {V : Type eV} {W : Type eW}
    (EL : V → T.obj L) (EM : W → T.obj M)
    (PL : V → T.obj A) (PM : W → T.obj B)
    (P : V → W) (Q : T.obj L → T.obj M)
    (hEL : EL = fun b => T.map φ (PL b))
    (hEM : EM = fun b => T.map ψ (PM b))
    (hQ : Q = fun b => T.map q b)
    (a : V) (hp : PM (P a) = T.map r (PL a)) : EM (P a) = Q (EL a) := by
  rw [hEM, hQ, hEL]
  change T.map ψ (PM (P a)) = T.map q (T.map φ (PL a))
  rw [hp]
  have hh := congrArg (fun f : A ⟶ M => T.map f (PL a)) hs
  rw [Functor.map_comp, Functor.map_comp] at hh
  exact hh


end CategoryTheory.Functor
