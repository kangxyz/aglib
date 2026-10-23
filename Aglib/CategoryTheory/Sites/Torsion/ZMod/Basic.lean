/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Canonical ZMod coefficients on the original abelian presheaf

Every original section group annihilated by `n` receives the native
`AddCommGroup.zmodModule` structure. Original restriction and coefficient
maps are the native `AddMonoidHom.toZModLinearMap` of the same additive maps.
The construction includes `n = 0`, where the native module is the integer module.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.TorsionZMod

universe u v w

/-- The original section group, with its native canonical ZMod-module structure. -/
def moduleObj (n : ℕ) (G : AddCommGrpCat.{w}) (hG : ∀ x : G, n • x = 0) :
    ModuleCat.{w} (ZMod n) :=
  letI := AddCommGroup.zmodModule hG
  ModuleCat.of (ZMod n) G

/-- The original additive coefficient map, made linear by the native ZMod API. -/
def moduleMap (n : ℕ) {G H : AddCommGrpCat.{w}}
    (hG : ∀ x : G, n • x = 0) (hH : ∀ x : H, n • x = 0) (f : G ⟶ H) :
    moduleObj n G hG ⟶ moduleObj n H hH := by
  letI := AddCommGroup.zmodModule hG
  letI := AddCommGroup.zmodModule hH
  exact ModuleCat.ofHom (f.hom.toZModLinearMap n)

@[simp]
theorem moduleMap_apply (n : ℕ) {G H : AddCommGrpCat.{w}}
    (hG : ∀ x : G, n • x = 0) (hH : ∀ x : H, n • x = 0)
    (f : G ⟶ H) (x : G) : moduleMap n hG hH f x = f x := rfl

theorem moduleMap_forget (n : ℕ) {G H : AddCommGrpCat.{w}}
    (hG : ∀ x : G, n • x = 0) (hH : ∀ x : H, n • x = 0) (f : G ⟶ H) :
    (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}).map
      (moduleMap n hG hH f) = f := rfl

@[simp]
theorem moduleMap_id (n : ℕ) {G : AddCommGrpCat.{w}} (hG : ∀ x : G, n • x = 0) :
    moduleMap n hG hG (𝟙 G) = 𝟙 (moduleObj n G hG) := by
  ext x
  rfl

@[simp]
theorem moduleMap_comp (n : ℕ) {G H K : AddCommGrpCat.{w}}
    (hG : ∀ x : G, n • x = 0) (hH : ∀ x : H, n • x = 0)
    (hK : ∀ x : K, n • x = 0) (f : G ⟶ H) (g : H ⟶ K) :
    moduleMap n hG hK (f ≫ g) = moduleMap n hG hH f ≫ moduleMap n hH hK g := by
  ext x
  rfl

variable {C : Type u} [Category.{v} C]

/-- The literal annihilation of the identity annihilates each original section. -/
theorem sectionsKilled_of_nsmul_id_eq_zero (n : ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hP : n • 𝟙 P = 0) (X : Cᵒᵖ) (x : P.obj X) : n • x = 0 := by
  have h := congrArg (fun f : P ⟶ P => f.app X x) hP
  exact h

/-- A genuine module presheaf on exactly the original section groups and restriction maps. -/
def presheaf (n : ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hP : ∀ (X : Cᵒᵖ) (x : P.obj X), n • x = 0) :
    Cᵒᵖ ⥤ ModuleCat.{w} (ZMod n) where
  obj X := moduleObj n (P.obj X) (hP X)
  map {X Y} f := moduleMap n (hP X) (hP Y) (P.map f)
  map_id X := by
    rw [P.map_id, moduleMap_id]
  map_comp f g := by
    rw [P.map_comp, moduleMap_comp]

@[simp]
theorem presheaf_map_apply (n : ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hP : ∀ (X : Cᵒᵖ) (x : P.obj X), n • x = 0)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : P.obj X) :
    (presheaf n P hP).map f x = P.map f x := rfl

/-- Forgetting the canonical scalar action recovers the original presheaf canonically. -/
def presheafUnderlyingIso (n : ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hP : ∀ (X : Cᵒᵖ) (x : P.obj X), n • x = 0) :
    presheaf n P hP ⋙ forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w} ≅ P :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

@[simp]
theorem presheafUnderlyingIso_hom_app (n : ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hP : ∀ (X : Cᵒᵖ) (x : P.obj X), n • x = 0) (X : Cᵒᵖ) :
    (presheafUnderlyingIso n P hP).hom.app X = 𝟙 (P.obj X) := rfl

/-- Every original coefficient morphism lifts canonically on the original sections. -/
def presheafMap (n : ℕ) {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (hP : ∀ (X : Cᵒᵖ) (x : P.obj X), n • x = 0)
    (hQ : ∀ (X : Cᵒᵖ) (x : Q.obj X), n • x = 0) (f : P ⟶ Q) :
    presheaf n P hP ⟶ presheaf n Q hQ where
  app X := moduleMap n (hP X) (hQ X) (f.app X)
  naturality {X Y} g := by
    ext x
    exact ConcreteCategory.congr_hom (f.naturality g) x

@[simp]
theorem presheafMap_app_apply (n : ℕ) {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (hP : ∀ (X : Cᵒᵖ) (x : P.obj X), n • x = 0)
    (hQ : ∀ (X : Cᵒᵖ) (x : Q.obj X), n • x = 0) (f : P ⟶ Q)
    (X : Cᵒᵖ) (x : P.obj X) : (presheafMap n hP hQ f).app X x = f.app X x := rfl

@[simp]
theorem presheafMap_id (n : ℕ) {P : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (hP : ∀ (X : Cᵒᵖ) (x : P.obj X), n • x = 0) :
    presheafMap n hP hP (𝟙 P) = 𝟙 (presheaf n P hP) := by
  ext X x
  rfl

@[simp]
theorem presheafMap_comp (n : ℕ) {P Q T : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (hP : ∀ (X : Cᵒᵖ) (x : P.obj X), n • x = 0)
    (hQ : ∀ (X : Cᵒᵖ) (x : Q.obj X), n • x = 0)
    (hT : ∀ (X : Cᵒᵖ) (x : T.obj X), n • x = 0) (f : P ⟶ Q) (g : Q ⟶ T) :
    presheafMap n hP hT (f ≫ g) = presheafMap n hP hQ f ≫ presheafMap n hQ hT g := by
  ext X x
  rfl

/-- The underlying coefficient morphism is the original morphism, with the same canonical
presheaf comparisons on both sides. -/
@[reassoc]
theorem presheafMap_underlying (n : ℕ) {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (hP : ∀ (X : Cᵒᵖ) (x : P.obj X), n • x = 0)
    (hQ : ∀ (X : Cᵒᵖ) (x : Q.obj X), n • x = 0) (f : P ⟶ Q) :
    Functor.whiskerRight (presheafMap n hP hQ f)
        (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}) ≫
      (presheafUnderlyingIso n Q hQ).hom = (presheafUnderlyingIso n P hP).hom ≫ f := by
  ext X x
  rfl

end CategoryTheory.TorsionZMod
