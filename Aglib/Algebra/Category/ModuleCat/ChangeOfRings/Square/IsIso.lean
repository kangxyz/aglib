/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Square
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.RestrictionSquare
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Isomorphisms of the original scalarized additive square

Bijectivity of the original additive vertical maps suffices; no independently
constructed linear equivalences or equalities between their records are needed.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped TensorProduct ChangeOfRings
universe u w
namespace ModuleCat

/-- Scalarize the same additive square and transfer invertibility from its
original lower mate, using bijectivity of the original vertical maps. -/
theorem extendAdditiveSquare_isIso_top_of_bijective
    {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
    (s : Square AddCommGrpCat.{max u w})
    (m₁ : Module R s.X₁) (m₂ : Module S s.X₂)
    (m₃ : Module R s.X₃) (m₄ : Module S s.X₄)
    (h₁₂ : letI := m₁; letI := m₂;
      ∀ (a : R) (x : s.X₁), s.f₁₂ (a • x) = σ a • s.f₁₂ x)
    (h₁₃ : letI := m₁; letI := m₃;
      ∀ (a : R) (x : s.X₁), s.f₁₃ (a • x) = a • s.f₁₃ x)
    (h₂₄ : letI := m₂; letI := m₄;
      ∀ (a : S) (x : s.X₂), s.f₂₄ (a • x) = a • s.f₂₄ x)
    (h₃₄ : letI := m₃; letI := m₄;
      ∀ (a : R) (x : s.X₃), s.f₃₄ (a • x) = σ a • s.f₃₄ x)
    (hl : Function.Bijective s.f₁₃) (hr : Function.Bijective s.f₂₄)
    (hb : IsIso (extendAdditiveSquare σ s m₁ m₂ m₃ m₄ h₁₂ h₁₃ h₂₄ h₃₄).f₃₄) :
    IsIso (extendAdditiveSquare σ s m₁ m₂ m₃ m₄ h₁₂ h₁₃ h₂₄ h₃₄).f₁₂ := by
  let := m₁
  let := m₂
  let := m₃
  let := m₄
  let l : ModuleCat.of R s.X₁ ⟶ ModuleCat.of R s.X₃ :=
    ModuleCat.ofHom { __ := s.f₁₃.hom, map_smul' := h₁₃ }
  let r : ModuleCat.of S s.X₂ ⟶ ModuleCat.of S s.X₄ :=
    ModuleCat.ofHom { __ := s.f₂₄.hom, map_smul' := h₂₄ }
  let : IsIso l := (ConcreteCategory.isIso_iff_bijective l).mpr hl
  let : IsIso r := (ConcreteCategory.isIso_iff_bijective r).mpr hr
  let t := extendAdditiveSquare σ s m₁ m₂ m₃ m₄ h₁₂ h₁₃ h₂₄ h₃₄
  let : IsIso t.f₁₃ := inferInstanceAs (IsIso ((extendScalars σ).map l))
  let : IsIso t.f₂₄ := inferInstanceAs (IsIso r)
  let : IsIso t.f₃₄ := hb
  exact t.isIso_top_of_other_edges

end ModuleCat
