/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.IntegralOpenOverlap
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Aglib.AlgebraicGeometry.Modules.Invertible.GenericUniqueness.OpenPrecomposition


/-!
# Actual overlap compatibility from original local unit squares

For an original arrow invertible on one actual nonempty open, original local
unit squares with a line target force compatibility on the native pullback
overlaps. Compatibility is proved, not supplied as a gluing hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

universe u v


open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem transport_square {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (e : F ≅ G) {P M N : C} (β : P ⟶ M) (t : P ⟶ N)
    (r : G.obj M ⟶ G.obj N) (h : G.map β ≫ r = G.map t) :
    F.map β ≫ e.hom.app M ≫ r ≫ e.inv.app N = F.map t := by
  rw [← Category.assoc (F.map β), e.hom.naturality β]
  rw [Category.assoc, ← Category.assoc (G.map β), h]
  rw [← Category.assoc, ← e.hom.naturality t, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

private theorem square_of_conjugate_eq {C : Type*} [Category C]
    {A B M N P Q : C} (eM : A ≅ M) (eN : B ≅ N) (eP : A ≅ P) (eQ : B ≅ Q)
    (r : M ⟶ N) (s : P ⟶ Q)
    (h : eM.hom ≫ r ≫ eN.inv = eP.hom ≫ s ≫ eQ.inv) :
    r ≫ eN.inv ≫ eQ.hom = eM.inv ≫ eP.hom ≫ s := by
  have hh := congrArg (fun z => eM.inv ≫ z ≫ eQ.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual local unit equations imply the literal native overlap compatibility. -/
theorem restrictionHomCompatible_of_openUnitSquares
    {X U : Scheme.{u}} [IsIntegral X] [Nonempty U] (j : U ⟶ X) [IsOpenImmersion j]
    {P M : X.Modules} (β : P ⟶ M) (L : Invertible.LineBundle X) (t : P ⟶ L.val)
    [IsIso ((Scheme.Modules.pullback j).map β)]
    {ι : Type v} (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (a i)] [∀ i, Nonempty (Y i)]
    (r : ∀ i, (Scheme.Modules.restrictFunctor (a i)).obj M ⟶
      (Scheme.Modules.restrictFunctor (a i)).obj L.val)
    (hr : ∀ i, (Scheme.Modules.restrictFunctor (a i)).map β ≫ r i =
      (Scheme.Modules.restrictFunctor (a i)).map t) :
    InternalHom.RestrictionHomCompatible a M L.val r := by
  intro i k
  let p := CategoryTheory.Limits.pullback.fst (a i) (a k)
  let q := CategoryTheory.Limits.pullback.snd (a i) (a k)
  let f := p ≫ a i
  let _ : Nonempty (CategoryTheory.Limits.pullback (a i) (a k) : Scheme) :=
    nonempty_openOverlap (a i) (a k)
  let e₁ := Scheme.Modules.restrictFunctorComp p (a i)
  let e₂ := Scheme.Modules.restrictFunctorCongr
    (CategoryTheory.Limits.pullback.condition (f := a i) (g := a k)) ≪≫
      Scheme.Modules.restrictFunctorComp q (a k)
  let r₁ := (Scheme.Modules.restrictFunctor p).map (r i)
  let r₂ := (Scheme.Modules.restrictFunctor q).map (r k)
  have h₁ : ((Scheme.Modules.restrictFunctor (a i) ⋙
      Scheme.Modules.restrictFunctor p).map β) ≫ r₁ =
      (Scheme.Modules.restrictFunctor (a i) ⋙ Scheme.Modules.restrictFunctor p).map t := by
    simpa only [r₁, CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
      CategoryTheory.Functor.map_comp] using
      congrArg (fun z => (Scheme.Modules.restrictFunctor p).map z) (hr i)
  have h₂ : ((Scheme.Modules.restrictFunctor (a k) ⋙
      Scheme.Modules.restrictFunctor q).map β) ≫ r₂ =
      (Scheme.Modules.restrictFunctor (a k) ⋙ Scheme.Modules.restrictFunctor q).map t := by
    simpa only [r₂, CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
      CategoryTheory.Functor.map_comp] using
      congrArg (fun z => (Scheme.Modules.restrictFunctor q).map z) (hr k)
  have hs₁ := transport_square _ _ e₁ β t r₁ h₁
  have hs₂ := transport_square _ _ e₂ β t r₂ h₂
  have he : e₁.hom.app M ≫ r₁ ≫ e₁.inv.app L.val =
      e₂.hom.app M ≫ r₂ ≫ e₂.inv.app L.val := by
    apply openUnitSquare_precomp_injective j f β L
    exact hs₁.trans hs₂.symm
  exact square_of_conjugate_eq (e₁.app M) (e₁.app L.val)
    (e₂.app M) (e₂.app L.val) r₁ r₂ he

/-- Original local unit squares on a genuine open cover give one unique global morphism. -/
theorem existsUnique_restrictionHom_of_openUnitSquares
    {X U : Scheme.{u}} [IsIntegral X] [Nonempty U] (j : U ⟶ X) [IsOpenImmersion j]
    {P M : X.Modules} (β : P ⟶ M) (L : Invertible.LineBundle X) (t : P ⟶ L.val)
    [IsIso ((Scheme.Modules.pullback j).map β)]
    {ι : Type v} (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (a i)] [∀ i, Nonempty (Y i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
    (r : ∀ i, (Scheme.Modules.restrictFunctor (a i)).obj M ⟶
      (Scheme.Modules.restrictFunctor (a i)).obj L.val)
    (hr : ∀ i, (Scheme.Modules.restrictFunctor (a i)).map β ≫ r i =
      (Scheme.Modules.restrictFunctor (a i)).map t) :
    ∃! g : M ⟶ L.val, ∀ i, (Scheme.Modules.restrictFunctor (a i)).map g = r i := by
  have hc := restrictionHomCompatible_of_openUnitSquares j β L t Y a r hr
  exact InternalHom.existsUnique_restrictionHom Y a hcover M L.val r hc

end AlgebraicGeometry.Scheme.Modules.Invertible
