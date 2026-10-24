/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleDirectImageValued
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleValuedDirectImageSquare

/-! # The original native direct-image square under the coefficient equivalence -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Inverse composition also retains the original valued comparison. -/
@[reassoc]
theorem moduleDirectImageCompIso_inv_valued {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (M : ModuleSheaf T Λ) :
    (moduleSheafEquivalence X Λ).inverse.map
        ((moduleDirectImageCompIso Λ f g).inv.app M) ≫
      (moduleDirectImageComparison (g ≫ f) Λ).hom.app M =
    (moduleDirectImageCompRightIso Λ f g).hom.app M ≫
      (moduleValuedDirectImageCompIso Λ f g).inv.app
        ((moduleSheafEquivalence T Λ).inverse.obj M) := by
  apply (Iso.inv_comp_eq ((moduleSheafEquivalence X Λ).inverse.mapIso
    ((moduleDirectImageCompIso Λ f g).app M))).2
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv ((moduleValuedDirectImageCompIso Λ f g).app
    ((moduleSheafEquivalence T Λ).inverse.obj M))).2
  exact (moduleDirectImageCompIso_hom_valued Λ f g M).symm

/-- The coefficient comparison respects transport along equality of scheme maps. -/
theorem moduleDirectImageComparison_eqToHom {X S : Scheme.{u}}
    {f g : X ⟶ S} (h : f = g) (M : ModuleSheaf X Λ) :
    (moduleSheafEquivalence S Λ).inverse.map
        ((eqToIso (congrArg (fun k => moduleDirectImage k Λ) h)).hom.app M) ≫
      (moduleDirectImageComparison g Λ).hom.app M =
    (moduleDirectImageComparison f Λ).hom.app M ≫
      (eqToIso (congrArg (fun k => moduleValuedDirectImage k Λ) h)).hom.app
        ((moduleSheafEquivalence X Λ).inverse.obj M) := by
  subst g
  simp

private theorem comparison_square
    {C D : Type*} [Category* C] [Category* D] (Q : C ⥤ D)
    {X₀ X₁ Y₀ Y₁ : C} {U₀ U₁ V₀ V₁ : D}
    (a : X₀ ≅ Y₀) (b : X₁ ≅ Y₁) (v₀ : U₀ ≅ V₀) (v₁ : U₁ ≅ V₁)
    (c₀ : Q.obj X₀ ⟶ U₀) (c₁ : Q.obj X₁ ⟶ U₁)
    (d₀ : Q.obj Y₀ ⟶ V₀) (d₁ : Q.obj Y₁ ⟶ V₁)
    (t : X₀ ⟶ X₁) (s : U₀ ⟶ U₁)
    (ha : Q.map a.inv ≫ c₀ = d₀ ≫ v₀.inv)
    (hb : Q.map b.hom ≫ d₁ = c₁ ≫ v₁.hom)
    (ht : Q.map t ≫ c₁ = c₀ ≫ s) :
    Q.map (a.inv ≫ t ≫ b.hom) ≫ d₁ =
      d₀ ≫ v₀.inv ≫ s ≫ v₁.hom := by
  simp only [Functor.map_comp, Category.assoc]
  rw [hb, ← Category.assoc (Q.map t) c₁, ht]
  simp only [Category.assoc]
  rw [← Category.assoc (Q.map a.inv) c₀, ha]
  simp only [Category.assoc]

private theorem inverse_iso_chain_app
    {C D : Type*} [Category* C] [Category* D]
    {F₀ F₁ F₂ F₃ : C ⥤ D} (a : F₁ ≅ F₀) (b : F₁ ≅ F₂)
    (c : F₂ ≅ F₃) (M : C) :
    (a.symm ≪≫ b ≪≫ c).hom.app M = a.inv.app M ≫ b.hom.app M ≫ c.hom.app M := rfl

/-- The native square retains its original functor-category composite. -/
theorem moduleDirectImageSquareIso_eq_comp {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    moduleDirectImageSquareIso Λ f f' g g' h =
      (moduleDirectImageCompIso Λ f g').symm ≪≫
        eqToIso (congrArg (fun k => moduleDirectImage k Λ) h.symm) ≪≫
        moduleDirectImageCompIso Λ g f' := rfl

/-- The native square on components is the original three-factor composite. -/
theorem moduleDirectImageSquareIso_hom_app {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (M : ModuleSheaf X' Λ) :
    (moduleDirectImageSquareIso Λ f f' g g' h).hom.app M =
      (moduleDirectImageCompIso Λ f g').inv.app M ≫
        (eqToIso (congrArg (fun k => moduleDirectImage k Λ) h.symm)).hom.app M ≫
        (moduleDirectImageCompIso Λ g f').hom.app M := by
  have he := congrArg (fun α :
      moduleDirectImage g' Λ ⋙ moduleDirectImage f Λ ≅
        moduleDirectImage f' Λ ⋙ moduleDirectImage g Λ => α.hom.app M)
    (moduleDirectImageSquareIso_eq_comp Λ f f' g g' h)
  exact he.trans (inverse_iso_chain_app (moduleDirectImageCompIso Λ f g')
    (eqToIso (congrArg (fun k => moduleDirectImage k Λ) h.symm))
    (moduleDirectImageCompIso Λ g f') M)

/-- The valued square on components is the original three-factor composite. -/
theorem moduleValuedDirectImageSquareIso_hom_comp_app {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (F : ModuleValuedSheaf X' Λ) :
    (moduleValuedDirectImageSquareIso f f' g g' h Λ).hom.app F =
      (moduleValuedDirectImageCompIso Λ f g').inv.app F ≫
        (eqToIso (congrArg (fun k => moduleValuedDirectImage k Λ) h.symm)).hom.app F ≫
        (moduleValuedDirectImageCompIso Λ g f').hom.app F := by
  have he := congrArg (fun e :
      moduleValuedDirectImage g' Λ ⋙ moduleValuedDirectImage f Λ ≅
        moduleValuedDirectImage f' Λ ⋙ moduleValuedDirectImage g Λ => e.hom.app F)
    (moduleValuedDirectImageSquareIso_comp f f' g g' h Λ)
  exact he.symm

/-- The original native direct-image square is the original valued site square after
transport through the actual constant-coefficient equivalence. -/
@[reassoc]
theorem moduleDirectImageSquareIso_hom_valued {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (M : ModuleSheaf X' Λ) :
    (moduleSheafEquivalence S Λ).inverse.map
        ((moduleDirectImageSquareIso Λ f f' g g' h).hom.app M) ≫
      (moduleDirectImageCompRightIso Λ g f').hom.app M =
    (moduleDirectImageCompRightIso Λ f g').hom.app M ≫
      (moduleValuedDirectImageSquareIso f f' g g' h Λ).hom.app
        ((moduleSheafEquivalence X' Λ).inverse.obj M) := by
  have hc := comparison_square (moduleSheafEquivalence S Λ).inverse
    ((moduleDirectImageCompIso Λ f g').app M)
    ((moduleDirectImageCompIso Λ g f').app M)
    ((moduleValuedDirectImageCompIso Λ f g').app
      ((moduleSheafEquivalence X' Λ).inverse.obj M))
    ((moduleValuedDirectImageCompIso Λ g f').app
      ((moduleSheafEquivalence X' Λ).inverse.obj M))
    ((moduleDirectImageComparison (g' ≫ f) Λ).hom.app M)
    ((moduleDirectImageComparison (f' ≫ g) Λ).hom.app M)
    ((moduleDirectImageCompRightIso Λ f g').hom.app M)
    ((moduleDirectImageCompRightIso Λ g f').hom.app M)
    ((eqToIso (congrArg (fun k => moduleDirectImage k Λ) h.symm)).hom.app M)
    ((eqToIso (congrArg (fun k => moduleValuedDirectImage k Λ) h.symm)).hom.app
      ((moduleSheafEquivalence X' Λ).inverse.obj M))
    (moduleDirectImageCompIso_inv_valued Λ f g' M)
    (moduleDirectImageCompIso_hom_valued Λ g f' M)
    (moduleDirectImageComparison_eqToHom Λ h.symm M)
  have hn := congrArg (fun a =>
    (moduleSheafEquivalence S Λ).inverse.map a ≫
      (moduleDirectImageCompRightIso Λ g f').hom.app M)
    (moduleDirectImageSquareIso_hom_app Λ f f' g g' h M)
  have hv := congrArg (fun a => (moduleDirectImageCompRightIso Λ f g').hom.app M ≫ a)
    (moduleValuedDirectImageSquareIso_hom_comp_app Λ f f' g g' h
      ((moduleSheafEquivalence X' Λ).inverse.obj M))
  exact hn.trans (hc.trans hv.symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
