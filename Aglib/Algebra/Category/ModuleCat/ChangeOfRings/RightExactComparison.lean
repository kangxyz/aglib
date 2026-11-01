/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Exactness
public import Mathlib.Algebra.FiveLemma

/-! # Right-exact scalar-change comparisons through original additive transports

The original scalar-extension row, the transported target row, and their two
squares are assembled before supplying geometric cohomology objects.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

universe u v₁ v₂ v₃

/-- Scalar extension and original additive transports form the complete
right-exact comparison. Isomorphisms on the first two objects give the original
isomorphism on the third object, without a flatness premise. -/
theorem isIso_of_rightExact_scalarChange_transport
    {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
    {M₁ M₂ M₃ : ModuleCat.{u + 1} R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)
    {N₁ N₂ N₃ : ModuleCat.{u + 1} S} (f' : N₁ ⟶ N₂) (g' : N₂ ⟶ N₃)
    {P₁ : Type v₁} {P₂ : Type v₂} {P₃ : Type v₃}
    [AddCommGroup P₁] [AddCommGroup P₂] [AddCommGroup P₃]
    (k : P₁ →+ P₂) (l : P₂ →+ P₃)
    (e₁ : N₁ →+ P₁) (e₂ : N₂ →+ P₂) (e₃ : N₃ →+ P₃)
    (he₁ : Function.Bijective e₁) (he₂ : Function.Bijective e₂)
    (he₃ : Function.Bijective e₃)
    (hn₁ : ∀ x, e₂ (f' x) = k (e₁ x)) (hn₂ : ∀ x, e₃ (g' x) = l (e₂ x))
    (a₁ : (extendScalars σ).obj M₁ ⟶ N₁)
    (a₂ : (extendScalars σ).obj M₂ ⟶ N₂)
    (a₃ : (extendScalars σ).obj M₃ ⟶ N₃)
    (sq₁ : (extendScalars σ).map f ≫ a₂ = a₁ ≫ f')
    (sq₂ : (extendScalars σ).map g ≫ a₃ = a₂ ≫ g')
    (hR : Function.Exact f g ∧ Function.Surjective g)
    (hP : Function.Exact k l ∧ Function.Surjective l)
    (ha₁ : IsIso a₁) (ha₂ : IsIso a₂) : IsIso a₃ := by
  have hN : Function.Exact f' g' ∧ Function.Surjective g' := by
    refine ⟨(AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
      f'.hom.toAddMonoidHom g'.hom.toAddMonoidHom k l e₁ e₂ e₃
      (AddMonoidHom.ext fun x => (hn₁ x).symm)
      (AddMonoidHom.ext fun x => (hn₂ x).symm) he₁.2 he₂ he₃.1).mpr hP.1, ?_⟩
    intro z
    obtain ⟨y, hy⟩ := hP.2 (e₃ z)
    obtain ⟨x, rfl⟩ := he₂.2 y
    exact ⟨x, he₃.1 ((hn₂ x).trans hy)⟩
  have hS := extendScalars_map_exact_of_surjective σ f g hR.1 hR.2
  rw [ConcreteCategory.isIso_iff_bijective] at ha₁ ha₂ ⊢
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
    ((extendScalars σ).map f).hom.toAddMonoidHom
    ((extendScalars σ).map g).hom.toAddMonoidHom
    f'.hom.toAddMonoidHom g'.hom.toAddMonoidHom
    a₁.hom.toAddMonoidHom a₂.hom.toAddMonoidHom a₃.hom.toAddMonoidHom
    (by ext x; exact (ConcreteCategory.congr_hom sq₁ x).symm)
    (by ext x; exact (ConcreteCategory.congr_hom sq₂ x).symm)
    hS.1 hN.1 ha₁.2 ha₂ hS.2 hN.2

end ModuleCat
