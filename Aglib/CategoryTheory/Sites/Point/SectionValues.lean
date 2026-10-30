/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Basic

/-! # Original section and germ map assembly

One supplied section functor, its actual comparison maps and original values
produce the complete section cancellation and germ square. No coefficient or
resolution realization is selected here.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v

namespace CategoryTheory

/-- The actual chart section map: inverse evaluation followed by the mapped component. -/
def chartSectionMapOfHom {C : Type*} [Category* C]
    (Γ : C ⥤ AddCommGrpCat.{v}) {A B : C} {Z : AddCommGrpCat.{v}}
    (E : Γ.obj A ≅ Z) (β : A ⟶ B) : Z ⟶ Γ.obj B :=
  E.inv ≫ Γ.map β

/-- The shared constructor retains its literal original factors. -/
theorem chartSectionMapOfHom_eq_comp {C : Type*} [Category* C]
    (Γ : C ⥤ AddCommGrpCat.{v}) {A B : C} {Z : AddCommGrpCat.{v}}
    (E : Γ.obj A ≅ Z) (β : A ⟶ B) :
    chartSectionMapOfHom Γ E β = E.inv ≫ Γ.map β := rfl

/-- Invertibility of the component gives invertibility of this same constructor. -/
theorem chartSectionMapOfHom_isIso {C : Type*} [Category* C]
    (Γ : C ⥤ AddCommGrpCat.{v}) {A B : C} {Z : AddCommGrpCat.{v}}
    (E : Γ.obj A ≅ Z) (β : A ⟶ B) (hβ : IsIso β) :
    IsIso (chartSectionMapOfHom Γ E β) := by
  let : IsIso β := hβ
  dsimp only [chartSectionMapOfHom]
  infer_instance

end CategoryTheory

namespace CategoryTheory

/-- The original represented-section construction from its actual edge and equivalence. -/
def representedSectionHomOfEquiv
    {A : Type*} [AddCommGroup A] {P Q : AddCommGrpCat.{v}}
    (edge : P ⟶ Q) (resolution : A ≃+ P) : A →+ Q :=
  edge.hom.comp resolution.toAddMonoidHom

/-- The actual unit followed by its section-level coefficient map. -/
def unitSectionMapOfHom {A B C : AddCommGrpCat.{v}}
    (unit : A ⟶ B) (coefficient : B ⟶ C) : A ⟶ C :=
  unit ≫ coefficient

end CategoryTheory

namespace CategoryTheory.OriginalSectionValues

/-- The existing additive iso gives injectivity of the original section map. -/
theorem iso_section_injective {A B : AddCommGrpCat.{v}} (e : A ≅ B)
    {x y : A} (h : e.hom x = e.hom y) : x = y :=
  e.addCommGroupIsoToAddEquiv.injective h

/-- Pointwise values identify the same actual additive homomorphisms. -/
theorem addHom_eq_of_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f g : A →+ B) (h : ∀ x, f x = g x) : f = g :=
  AddMonoidHom.ext h

/-- Conjugate the original source equivalence without a second section presentation. -/
theorem chartHom_normalize
    {A B C D : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D]
    (e : A ≃+ B) (s : A →+ C) (m : C →+ D) (t : B →+ D)
    (source : B →+ C) (hsource : source = s.comp e.symm.toAddMonoidHom)
    (h : m.comp s = t.comp e.toAddMonoidHom) : m.comp source = t := by
  subst source
  apply AddMonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun h (e.symm x)
  exact hx.trans (congrArg t (e.apply_symm_apply x))

/-- Compose the two original coefficient value laws through the same section functor. -/
theorem mapped_coefficient_hom
    {C : Type*} [Category* C] (Γ : C ⥤ AddCommGrpCat.{v})
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    {P R T : Type*} [AddCommGroup P] [AddCommGroup R] [AddCommGroup T]
    (a : P →+ Γ.obj A) (b : R →+ Γ.obj B) (c : T →+ Γ.obj D)
    (r : P →+ R) (t : R →+ T)
    (hf : (Γ.map f).hom.comp a = b.comp r)
    (hg : (Γ.map g).hom.comp b = c.comp t) :
    (Γ.map (f ≫ g)).hom.comp a = c.comp (t.comp r) := by
  rw [Γ.map_comp]
  calc
    _ = (Γ.map g).hom.comp ((Γ.map f).hom.comp a) := rfl
    _ = (Γ.map g).hom.comp (b.comp r) := congrArg ((Γ.map g).hom.comp) hf
    _ = ((Γ.map g).hom.comp b).comp r := rfl
    _ = (c.comp t).comp r := congrArg (fun z => z.comp r) hg
    _ = _ := rfl

/-- Cancel the actual invertible target section map in the original square. -/
theorem sectionHom_cancel
    {A B C D : AddCommGrpCat.{v}} (k : A ⟶ B) (a : A ⟶ C)
    (b : B ⟶ D) (c : C ⟶ D) [IsIso b]
    {P R : Type*} [AddCommGroup P] [AddCommGroup R]
    (source : P →+ A) (target : R →+ B) (r : P →+ R)
    (sourceHigher : P →+ C) (targetHigher : R →+ D)
    (hsquare : k ≫ b = a ≫ c)
    (hsource : a.hom.comp source = sourceHigher)
    (hglobal : c.hom.comp sourceHigher = targetHigher.comp r)
    (htarget : b.hom.comp target = targetHigher) :
    k.hom.comp source = target.comp r := by
  have hh : b.hom.comp (k.hom.comp source) = b.hom.comp (target.comp r) := by
    calc
      _ = (k ≫ b).hom.comp source := rfl
      _ = (a ≫ c).hom.comp source := congrArg (fun z => z.hom.comp source) hsquare
      _ = c.hom.comp (a.hom.comp source) := rfl
      _ = c.hom.comp sourceHigher := congrArg c.hom.comp hsource
      _ = targetHigher.comp r := hglobal
      _ = (b.hom.comp target).comp r := congrArg (fun z => z.comp r) htarget.symm
      _ = _ := rfl
  apply AddMonoidHom.ext
  intro x
  exact iso_section_injective (asIso b) (DFunLike.congr_fun hh x)

/-- The original section square and unit/germ laws give the complete germ square. -/
theorem germHom_of_sectionHom
    {A B C D E F : AddCommGrpCat.{v}}
    (a : A ⟶ B) (σ : B ⟶ D) (u : A ⟶ C) (b : C ⟶ E)
    (c : C ⟶ D) (β : D ⟶ F) (t : E ⟶ F) (k : A ⟶ E)
    (hk : k = u ≫ b) (hu : a ≫ σ = u ≫ c) (hn : c ≫ β = b ≫ t)
    {P R : Type*} [AddCommGroup P] [AddCommGroup R]
    (source : P →+ A) (target : R →+ E) (r : P →+ R)
    (sourceGerm : P →+ B) (targetGerm : R →+ F)
    (hsource : sourceGerm = a.hom.comp source)
    (htarget : targetGerm = t.hom.comp target)
    (hsection : k.hom.comp source = target.comp r) :
    (σ ≫ β).hom.comp sourceGerm = targetGerm.comp r := by
  have hd : a ≫ σ ≫ β = k ≫ t := by
    calc
      _ = (a ≫ σ) ≫ β := (Category.assoc _ _ _).symm
      _ = (u ≫ c) ≫ β := congrArg (fun z => z ≫ β) hu
      _ = u ≫ (c ≫ β) := Category.assoc _ _ _
      _ = u ≫ (b ≫ t) := congrArg (fun z => u ≫ z) hn
      _ = (u ≫ b) ≫ t := (Category.assoc _ _ _).symm
      _ = k ≫ t := congrArg (fun z => z ≫ t) hk.symm
  calc
    _ = (σ ≫ β).hom.comp (a.hom.comp source) := congrArg (σ ≫ β).hom.comp hsource
    _ = (a ≫ σ ≫ β).hom.comp source := rfl
    _ = (k ≫ t).hom.comp source := congrArg (fun z => z.hom.comp source) hd
    _ = t.hom.comp (k.hom.comp source) := rfl
    _ = t.hom.comp (target.comp r) := congrArg t.hom.comp hsection
    _ = (t.hom.comp target).comp r := rfl
    _ = _ := congrArg (fun z => z.comp r) htarget.symm

/-- Evaluate that same whole additive germ equation at the original element. -/
theorem germHom_apply
    {P R : Type*} [AddCommGroup P] [AddCommGroup R]
    {A B C : AddCommGrpCat.{v}} (σ : A ⟶ B) (β : B ⟶ C)
    (source : P →+ A) (target : R →+ C) (r : P →+ R)
    (h : (σ ≫ β).hom.comp source = target.comp r) (x : P) :
    β (σ (source x)) = target (r x) :=
  DFunLike.congr_fun h x

end CategoryTheory.OriginalSectionValues
