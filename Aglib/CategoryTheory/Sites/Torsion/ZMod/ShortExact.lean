/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Sheaf
public import Aglib.Algebra.Category.ModuleCat.Sheaf.UnderlyingExact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian

/-! # Original bounded short exact sequences as genuine ZMod sheaves

An extension is killed by the product of the two endpoint bounds. Canonical
scalar conversion keeps the original objects and arrows, and its underlying
short complex is canonically the original one. Exactness is reflected by the
original faithful underlying functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

/-- The product of endpoint scalar annihilators kills the original middle
term of a short exact sequence in any abelian category. -/
theorem ShortExact.nsmul_id_mul_eq_zero
    {D : Type*} [Category D] [Abelian D] {S : ShortComplex D} (hS : S.ShortExact)
    (n m : ℕ) (h₁ : n • 𝟙 S.X₁ = 0) (h₃ : m • 𝟙 S.X₃ = 0) :
    (n * m) • 𝟙 S.X₂ = 0 := by
  have := hS.mono_f
  have hg : (m • 𝟙 S.X₂) ≫ S.g = 0 := by
    rw [Preadditive.nsmul_comp, Category.id_comp,
      ← Category.comp_id S.g, ← Preadditive.comp_nsmul, h₃, comp_zero]
  let l := hS.exact.lift (m • 𝟙 S.X₂) hg
  have hl : l ≫ S.f = m • 𝟙 S.X₂ := hS.exact.lift_f _ _
  calc
    (n * m) • 𝟙 S.X₂ = n • (m • 𝟙 S.X₂) := mul_smul n m _
    _ = n • (l ≫ S.f) := congrArg (n • ·) hl.symm
    _ = l ≫ (n • S.f) := (Preadditive.comp_nsmul _ _ _).symm
    _ = l ≫ ((n • 𝟙 S.X₁) ≫ S.f) := by
      rw [Preadditive.nsmul_comp, Category.id_comp]
    _ = 0 := by rw [h₁, zero_comp, comp_zero]

end CategoryTheory.ShortComplex

namespace CategoryTheory.TorsionZMod

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)
  [HasSheafify J AddCommGrpCat.{max u v}]

attribute [local instance] ModuleCat.Sheaf.hasSheafify

local instance underlying_preservesZeroMorphisms :
    (ModuleCat.Sheaf.underlying (ZMod n) J).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Canonical scalar lift of all three original objects and both arrows. -/
def shortComplex (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}))
    (h₁ : n • 𝟙 S.X₁ = 0) (h₂ : n • 𝟙 S.X₂ = 0) (h₃ : n • 𝟙 S.X₃ = 0) :
    ShortComplex (Sheaf J (ModuleCat.{max u v} (ZMod n))) :=
  ShortComplex.mk (sheafMap J n h₁ h₂ S.f) (sheafMap J n h₂ h₃ S.g) (by
    apply ObjectProperty.hom_ext
    ext V x
    exact congrArg (fun a : S.X₁ ⟶ S.X₃ => a.hom.app V x) S.zero)

/-- Scalar forgetting recovers the literal original short complex, through
its original natural coefficient comparisons. -/
def shortComplexUnderlyingIso (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}))
    (h₁ : n • 𝟙 S.X₁ = 0) (h₂ : n • 𝟙 S.X₂ = 0) (h₃ : n • 𝟙 S.X₃ = 0) :
    (shortComplex J n S h₁ h₂ h₃).map (ModuleCat.Sheaf.underlying (ZMod n) J) ≅ S :=
  ShortComplex.isoMk (sheafUnderlyingIso J n S.X₁ h₁)
    (sheafUnderlyingIso J n S.X₂ h₂) (sheafUnderlyingIso J n S.X₃ h₃)
    (sheafMap_underlying J n h₁ h₂ S.f).symm
    (sheafMap_underlying J n h₂ h₃ S.g).symm

/-- The same original short exact sequence is short exact after canonical
bounded scalar conversion. -/
theorem shortComplex_shortExact (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}))
    (h₁ : n • 𝟙 S.X₁ = 0) (h₂ : n • 𝟙 S.X₂ = 0) (h₃ : n • 𝟙 S.X₃ = 0)
    (hS : S.ShortExact) : (shortComplex J n S h₁ h₂ h₃).ShortExact := by
  apply ShortExact.reflects_shortExact_of_faithful (ModuleCat.Sheaf.underlying (ZMod n) J)
  exact (ShortComplex.shortExact_iff_of_iso
    (shortComplexUnderlyingIso J n S h₁ h₂ h₃)).mpr hS

end CategoryTheory.TorsionZMod
