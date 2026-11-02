/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange

/-! # Original horizontal exchange composition and congruence

The native horizontal-pasting identity implies composition of invertible
original derived exchanges. Equality of the displayed scheme arrows transports
the original maps without unfolding the native mate or derived adjunctions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u dX₀ dX₁ dX₂ dS₀ dS₁ dS₂

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

section Horizontal

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
  [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X₀)]
  [HasDerivedCategory.{dX₁} (AbelianSheaf.{u, u + 1} X₁)]
  [HasDerivedCategory.{dX₂} (AbelianSheaf.{u, u + 1} X₂)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S₀)]
  [HasDerivedCategory.{dS₁} (AbelianSheaf.{u, u + 1} S₁)]
  [HasDerivedCategory.{dS₂} (AbelianSheaf.{u, u + 1} S₂)]
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)

/-- Native horizontal pasting preserves invertibility of original derived exchanges. -/
theorem derivedBaseChangeMap_isIso_hComp
    [IsIso (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁)]
    [IsIso (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)] :
    IsIso (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e) := by
  have (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X₀)) :
      IsIso ((derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).app K) := by
    apply (isIso_comp_right_iff _
      ((derivedDirectImage f₂).map ((derivedInverseImageCompIso h₁ h₂).hom.app K))).mp
    rw [← derivedBaseChangeMap_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e K]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Horizontal

private theorem dependentProperty_congr
    {A B : Sort*} {Q : A → B → Prop} (P : ∀ a b, Q a b → Prop)
    {a₁ a₂ : A} {b₁ b₂ : B} (e₁ : Q a₁ b₁) (e₂ : Q a₂ b₂)
    (ha : a₁ = a₂) (hb : b₁ = b₂) : P a₁ b₁ e₁ ↔ P a₂ b₂ e₂ := by
  subst a₂
  subst b₂
  rfl

section Congruence

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX₁} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS₁} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S')
  (g₁ g₂ : S' ⟶ S) (k₁ k₂ : X' ⟶ X)
  (e₁ : f' ≫ g₁ = k₁ ≫ f) (e₂ : f' ≫ g₂ = k₂ ≫ f)

/-- Equality of horizontal arrows transports the actual whole derived exchange. -/
theorem derivedBaseChangeMap_isIso_congr (hg : g₁ = g₂) (hk : k₁ = k₂) :
    IsIso (derivedBaseChangeMap f f' g₁ k₁ e₁) ↔
      IsIso (derivedBaseChangeMap f f' g₂ k₂ e₂) :=
  dependentProperty_congr
    (fun g k h => IsIso (derivedBaseChangeMap f f' g k h)) e₁ e₂ hg hk

omit [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX₁} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS₁} (AbelianSheaf.{u, u + 1} S')] in
/-- Equality of horizontal arrows transports the actual higher exchange component. -/
theorem higherBaseChangeMap_isIso_app_congr (hg : g₁ = g₂) (hk : k₁ = k₂)
    (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((higherBaseChangeMap f f' g₁ k₁ e₁ q).app F) ↔
      IsIso ((higherBaseChangeMap f f' g₂ k₂ e₂ q).app F) :=
  dependentProperty_congr
    (fun g k h => IsIso ((higherBaseChangeMap f f' g k h q).app F)) e₁ e₂ hg hk

end Congruence

end AlgebraicGeometry.Scheme.EtaleCohomology
