/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Localization.Monoidal.Braided

/-!
# The localized monoidal structure through chosen isomorphisms

Let `L : C ⥤ D` be a localization functor for a monoidal class `W`, and give
`LocalizedMonoidal L W ε` Mathlib's localized monoidal structure, with tensor comparison
`Localization.Monoidal.μ`. For objects `Mᵢ` with chosen isomorphisms `eᵢ : L.obj Aᵢ ≅ Mᵢ`,
`μOf e₁ e₂ : M₁ ⊗ M₂ ≅ L.obj (A₁ ⊗ A₂)` transports `μ` along them.

This file expresses the localized tensor maps, associator, unitors and braiding through `μOf`
as images under `L` of the corresponding structure maps of `C`. These identities have exactly
the shape of the equations of `CategoryTheory.Monoidal.InducingFunctorData` and of the braiding
condition of `CategoryTheory.BraidedCategory.ofFaithful` for a structure on `D` whose tensor
objects are `L.obj (A₁ ⊗ A₂)`. They are stated for arbitrary objects, morphisms and
isomorphisms. The current consumer is the scheme-module tensor structure in
`Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Basic`.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory.Localization.Monoidal

open Category MonoidalCategory BraidedCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
  (L : C ⥤ D) (W : MorphismProperty C) [W.IsMonoidal] [L.IsLocalization W]
  {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

/-- The localized tensor comparison `μ`, transported along isomorphisms
`eᵢ : L'.obj Aᵢ ≅ Mᵢ`. -/
def μOf {A₁ A₂ : C} {M₁ M₂ : LocalizedMonoidal L W ε}
    (e₁ : (L').obj A₁ ≅ M₁) (e₂ : (L').obj A₂ ≅ M₂) : M₁ ⊗ M₂ ≅ (L').obj (A₁ ⊗ A₂) :=
  (e₁.symm ⊗ᵢ e₂.symm) ≪≫ μ L W ε A₁ A₂

variable {L W ε}

lemma μOf_hom {A₁ A₂ : C} {M₁ M₂ : LocalizedMonoidal L W ε}
    (e₁ : (L').obj A₁ ≅ M₁) (e₂ : (L').obj A₂ ≅ M₂) :
    (μOf L W ε e₁ e₂).hom = (e₁.inv ⊗ₘ e₂.inv) ≫ (μ L W ε A₁ A₂).hom := rfl

lemma μOf_inv {A₁ A₂ : C} {M₁ M₂ : LocalizedMonoidal L W ε}
    (e₁ : (L').obj A₁ ≅ M₁) (e₂ : (L').obj A₂ ≅ M₂) :
    (μOf L W ε e₁ e₂).inv = (μ L W ε A₁ A₂).inv ≫ (e₁.hom ⊗ₘ e₂.hom) := rfl

/-- Naturality of `μ` for tensor products of morphisms. -/
@[reassoc]
lemma μ_natural_tensorHom {A₁ A₂ B₁ B₂ : C} (h₁ : A₁ ⟶ B₁) (h₂ : A₂ ⟶ B₂) :
    ((L').map h₁ ⊗ₘ (L').map h₂) ≫ (μ L W ε B₁ B₂).hom =
      (μ L W ε A₁ A₂).hom ≫ (L').map (h₁ ⊗ₘ h₂) := by
  simp only [tensorHom_def, assoc, μ_natural_right, μ_natural_left_assoc, Functor.map_comp]

/-- The image of a tensor product of morphisms, through `μOf`. -/
lemma map_tensorHom_eq {A₁ A₂ B₁ B₂ : C} {M₁ M₂ N₁ N₂ : LocalizedMonoidal L W ε}
    (e₁ : (L').obj A₁ ≅ M₁) (e₂ : (L').obj A₂ ≅ M₂)
    (e₁' : (L').obj B₁ ≅ N₁) (e₂' : (L').obj B₂ ≅ N₂)
    {h₁ : A₁ ⟶ B₁} {h₂ : A₂ ⟶ B₂} {f₁ : M₁ ⟶ N₁} {f₂ : M₂ ⟶ N₂}
    (w₁ : (L').map h₁ ≫ e₁'.hom = e₁.hom ≫ f₁) (w₂ : (L').map h₂ ≫ e₂'.hom = e₂.hom ≫ f₂) :
    (L').map (h₁ ⊗ₘ h₂) =
      (μOf L W ε e₁ e₂).inv ≫ (f₁ ⊗ₘ f₂) ≫ (μOf L W ε e₁' e₂').hom := by
  have k₁ : (L').map h₁ = e₁.hom ≫ f₁ ≫ e₁'.inv := by
    rw [← reassoc_of% w₁, Iso.hom_inv_id, comp_id]
  have k₂ : (L').map h₂ = e₂.hom ≫ f₂ ≫ e₂'.inv := by
    rw [← reassoc_of% w₂, Iso.hom_inv_id, comp_id]
  rw [μOf_inv, μOf_hom, assoc, Iso.eq_inv_comp, ← μ_natural_tensorHom, k₁, k₂]
  simp only [← tensorHom_comp_tensorHom, assoc]

/-- Precomposing the inverse of `μOf e e₃` with the image of `u ▷ A₃`, where `L'.map u` is
inverse to `e`. -/
lemma map_whiskerRight_comp_μOf_inv {A S A₃ : C} {M₃ : LocalizedMonoidal L W ε}
    (u : A ⟶ S) (e : (L').obj S ≅ (L').obj A) (e₃ : (L').obj A₃ ≅ M₃)
    (hu : (L').map u ≫ e.hom = 𝟙 _) :
    (L').map (u ▷ A₃) ≫ (μOf L W ε e e₃).inv = (μOf L W ε (Iso.refl _) e₃).inv := by
  rw [μOf_inv, μOf_inv, ← μ_inv_natural_left_assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
    hu, id_comp, Iso.refl_hom]

/-- `μOf e₁ e` followed by nothing equals `μOf e₁ (Iso.refl _)` followed by the image of
`A₁ ◁ v`, where `L'.map v` is inverse to `e`. -/
lemma μOf_hom_eq_comp_map_whiskerLeft {A₁ A T : C} {M₁ : LocalizedMonoidal L W ε}
    (e₁ : (L').obj A₁ ≅ M₁) (v : A ⟶ T) (e : (L').obj T ≅ (L').obj A)
    (hv : (L').map v ≫ e.hom = 𝟙 _) :
    (μOf L W ε e₁ e).hom = (μOf L W ε e₁ (Iso.refl _)).hom ≫ (L').map (A₁ ◁ v) := by
  have hv' : e.inv = (L').map v := ((Iso.comp_hom_eq_id e).mp hv).symm
  rw [μOf_hom, μOf_hom, hv', assoc, ← μ_natural_right, Iso.refl_inv, ← id_tensorHom,
    tensorHom_comp_tensorHom_assoc, comp_id, id_comp]

/-- The localized associator at `Mᵢ`, conjugated by the `μOf`, is the image of the associator
of `C`. -/
@[reassoc]
lemma μOf_associator_eq {A₁ A₂ A₃ : C} {M₁ M₂ M₃ : LocalizedMonoidal L W ε}
    (e₁ : (L').obj A₁ ≅ M₁) (e₂ : (L').obj A₂ ≅ M₂) (e₃ : (L').obj A₃ ≅ M₃) :
    (μOf L W ε (Iso.refl _) e₃).inv ≫ ((μOf L W ε e₁ e₂).inv ⊗ₘ 𝟙 M₃) ≫
        (α_ M₁ M₂ M₃).hom ≫ (𝟙 M₁ ⊗ₘ (μOf L W ε e₂ e₃).hom) ≫
          (μOf L W ε e₁ (Iso.refl _)).hom =
      (L').map (α_ A₁ A₂ A₃).hom := by
  have nat : (α_ M₁ M₂ M₃).hom = ((e₁.inv ⊗ₘ e₂.inv) ⊗ₘ e₃.inv) ≫
      (α_ ((L').obj A₁) ((L').obj A₂) ((L').obj A₃)).hom ≫ (e₁.hom ⊗ₘ e₂.hom ⊗ₘ e₃.hom) := by
    rw [associator_naturality_assoc]
    simp only [tensorHom_comp_tensorHom, Iso.inv_hom_id, id_tensorHom_id, comp_id]
  rw [nat, associator_hom_app]
  simp only [μOf_inv, μOf_hom, Iso.refl_hom, Iso.refl_inv, assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom_assoc, id_comp, comp_id, Iso.hom_inv_id, Iso.inv_hom_id,
    Iso.inv_hom_id_assoc, id_tensorHom_id]

/-- The associator equation of `Monoidal.InducingFunctorData`, through `μOf`: for maps `u`,
`v` whose images are inverse to `e₁₂`, `e₂₃`, the conjugated localized associator, precomposed
with the image of `u ▷ A₃`, is the image of the associator of `C` followed by that of
`A₁ ◁ v`. -/
lemma map_whiskerRight_comp_associator_eq {A₁ A₂ A₃ S T : C}
    {M₁ M₂ M₃ : LocalizedMonoidal L W ε}
    (e₁ : (L').obj A₁ ≅ M₁) (e₂ : (L').obj A₂ ≅ M₂) (e₃ : (L').obj A₃ ≅ M₃)
    (u : A₁ ⊗ A₂ ⟶ S) (v : A₂ ⊗ A₃ ⟶ T)
    (e₁₂ : (L').obj S ≅ (L').obj (A₁ ⊗ A₂)) (e₂₃ : (L').obj T ≅ (L').obj (A₂ ⊗ A₃))
    (hu : (L').map u ≫ e₁₂.hom = 𝟙 _) (hv : (L').map v ≫ e₂₃.hom = 𝟙 _) :
    (L').map (u ▷ A₃) ≫
      (((μOf L W ε e₁₂ e₃).symm ≪≫ ((μOf L W ε e₁ e₂).symm ⊗ᵢ Iso.refl _)) ≪≫
        α_ M₁ M₂ M₃ ≪≫ ((Iso.refl _ ⊗ᵢ μOf L W ε e₂ e₃) ≪≫ μOf L W ε e₁ e₂₃)).hom =
      (L').map (α_ A₁ A₂ A₃).hom ≫ (L').map (A₁ ◁ v) := by
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, assoc]
  rw [reassoc_of% (map_whiskerRight_comp_μOf_inv u e₁₂ e₃ hu),
    μOf_hom_eq_comp_map_whiskerLeft e₁ v e₂₃ hv, μOf_associator_eq_assoc]

/-- The left unitor equation of `Monoidal.InducingFunctorData`, through `μOf`. -/
lemma map_leftUnitor_hom_comp {A : C} {M : LocalizedMonoidal L W ε} (e : (L').obj A ≅ M) :
    (L').map (λ_ A).hom ≫ e.hom =
      (((μOf L W ε (M₁ := 𝟙_ (LocalizedMonoidal L W ε)) (ε' L W ε) e).symm ≪≫
        ((Iso.refl (𝟙_ (LocalizedMonoidal L W ε))).symm ⊗ᵢ Iso.refl M)) ≪≫ λ_ M).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Iso.refl_inv,
    id_tensorHom_id, id_comp, μOf_inv, assoc]
  rw [Iso.eq_inv_comp, tensorHom_def, assoc, leftUnitor_naturality, leftUnitor_hom_app,
    assoc, assoc, hom_inv_whiskerRight_assoc]

/-- The right unitor equation of `Monoidal.InducingFunctorData`, through `μOf`. -/
lemma map_rightUnitor_hom_comp {A : C} {M : LocalizedMonoidal L W ε} (e : (L').obj A ≅ M) :
    (L').map (ρ_ A).hom ≫ e.hom =
      (((μOf L W ε (M₂ := 𝟙_ (LocalizedMonoidal L W ε)) e (ε' L W ε)).symm ≪≫
        (Iso.refl M ⊗ᵢ (Iso.refl (𝟙_ (LocalizedMonoidal L W ε))).symm)) ≪≫ ρ_ M).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Iso.refl_inv,
    id_tensorHom_id, id_comp, μOf_inv, assoc]
  rw [Iso.eq_inv_comp, tensorHom_def', assoc, rightUnitor_naturality, rightUnitor_hom_app,
    assoc, assoc, whiskerLeft_hom_inv_assoc]

section Braided

variable [BraidedCategory C]

/-- The braiding condition of `BraidedCategory.ofFaithful`, through `μOf`. -/
lemma μOf_hom_comp_map_braiding {A₁ A₂ : C} {M₁ M₂ : LocalizedMonoidal L W ε}
    (e₁ : (L').obj A₁ ≅ M₁) (e₂ : (L').obj A₂ ≅ M₂) :
    (μOf L W ε e₁ e₂).hom ≫ (L').map (β_ A₁ A₂).hom =
      (β_ M₁ M₂).hom ≫ (μOf L W ε e₂ e₁).hom := by
  rw [μOf_hom, μOf_hom, assoc, Functor.map_braiding]
  change (e₁.inv ⊗ₘ e₂.inv) ≫ Functor.LaxMonoidal.μ (L') A₁ A₂ ≫
      Functor.OplaxMonoidal.δ (L') A₁ A₂ ≫ (β_ _ _).hom ≫ Functor.LaxMonoidal.μ (L') A₂ A₁ =
    (β_ M₁ M₂).hom ≫ (e₂.inv ⊗ₘ e₁.inv) ≫ Functor.LaxMonoidal.μ (L') A₂ A₁
  rw [Functor.Monoidal.μ_δ_assoc, braiding_naturality_assoc]

end Braided

end CategoryTheory.Localization.Monoidal
