/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleSourceExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangePasting

/-! # Original exchange under composition of its source -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {V P U Y X : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
  (p : P ⟶ U) (q : P ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  (h : p ≫ j = q ≫ f) (e : V ⟶ P)
  (he : (e ≫ p) ≫ j = (e ≫ q) ≫ f)

private theorem source_map_congr (f₀ f₁ : Y ⟶ X) (hf : f₀ = f₁)
    (p₀ : V ⟶ U) (q₀ : V ⟶ Y) (h₀ : p₀ ≫ j = q₀ ≫ f₀)
    (h₁ : p₀ ≫ j = q₀ ≫ f₁) (M : ModuleSheaf Y Λ) :
    (moduleInverseImage j Λ).map
        ((eqToIso (congrArg (fun k => moduleDirectImage k Λ) hf)).hom.app M) ≫
      (moduleBaseChangeMap Λ f₁ p₀ j q₀ h₁).app M =
    (moduleBaseChangeMap Λ f₀ p₀ j q₀ h₀).app M := by
  exact SourceChange.indexed_map_transport
    (fun k : Y ⟶ X => moduleDirectImage k Λ)
    (moduleInverseImage j Λ) (moduleInverseImage q₀ Λ ⋙ moduleDirectImage p₀ Λ)
    (fun k => p₀ ≫ j = q₀ ≫ k)
    (fun k hk => moduleBaseChangeMap Λ k p₀ j q₀ hk) hf h₀ h₁ M

/-- Source pasting retains the original source adjunction unit, before any invertibility. -/
@[reassoc]
theorem moduleBaseChangeMap_source_comp (M : ModuleSheaf Y Λ) :
    (moduleBaseChangeMap Λ f (e ≫ p) j (e ≫ q) he).app M ≫
      (moduleDirectImageCompIso Λ p e).hom.app ((moduleInverseImage (e ≫ q) Λ).obj M) ≫
      (moduleDirectImage p Λ).map ((moduleDirectImage e Λ).map
        ((moduleInverseImageCompIso Λ q e).hom.app M)) =
    (moduleBaseChangeMap Λ f p j q h).app M ≫
      (moduleDirectImage p Λ).map
        ((moduleInverseImageAdjunction e Λ).unit.app ((moduleInverseImage q Λ).obj M)) := by
  exact SourceChange.source_pasting
    (moduleDirectImage (𝟙 Y ≫ f) Λ) (moduleDirectImage f Λ)
    (moduleDirectImage (𝟙 Y) Λ) (moduleInverseImage j Λ) (moduleInverseImage q Λ)
    (moduleInverseImageAdjunction e Λ) (moduleDirectImage p Λ)
    (moduleDirectImage (e ≫ p) Λ) (moduleInverseImage (e ≫ q) Λ)
    (moduleDirectImageCompIso Λ f (𝟙 Y)) (moduleDirectImageIdIso Λ Y)
    (eqToIso (congrArg (fun k : Y ⟶ X => moduleDirectImage k Λ) (Category.id_comp f)))
    (moduleDirectImageCompIso Λ p e) (moduleInverseImageCompIso Λ q e)
    (moduleBaseChangeMap Λ f p j q h)
    (moduleBaseChangeMap Λ (𝟙 Y) e q (e ≫ q) (Category.comp_id (e ≫ q)).symm)
    (moduleBaseChangeMap Λ (𝟙 Y ≫ f) (e ≫ p) j (e ≫ q)
      (he.trans (by rw [Category.id_comp])))
    (moduleBaseChangeMap Λ f (e ≫ p) j (e ≫ q) he)
    (moduleDirectImageCompIso_comp_id Λ f)
    (fun M => by
      simpa only [moduleSourceInverseImageIso, SourceChange.sourceComparison_refl] using
        moduleBaseChangeMap_source Λ q e (e ≫ q) rfl M)
    (moduleBaseChangeMap_vComp Λ f (𝟙 Y) p e j q (e ≫ q) h
      (Category.comp_id (e ≫ q)).symm (he.trans (by rw [Category.id_comp])))
    (source_map_congr Λ j (𝟙 Y ≫ f) f (Category.id_comp f)
      (e ≫ p) (e ≫ q) (he.trans (by rw [Category.id_comp])) he) M

end AlgebraicGeometry.Scheme.EtaleCohomology
