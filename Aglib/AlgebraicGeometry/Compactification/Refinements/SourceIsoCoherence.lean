/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIso

/-!
# Composition of original source transports

The comparison maps are identities on the original ambient schemes. This
supplies the actual endpoint identifications for normalized-base-change pasting.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X₀ X₁ X₂ S : Scheme.{u}} (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
  (e₁ : X₁ ≅ X₀) (e₂ : X₂ ≅ X₁) (h₁ : e₁.hom ≫ f₀ = f₁)
  (h₂ : e₂.hom ≫ f₁ = f₂)

include h₁ h₂ in
/-- The composed original source isomorphism preserves the original base map. -/
lemma sourceIso_comp_fac : (e₂ ≪≫ e₁).hom ≫ f₀ = f₂ :=
  (Category.assoc _ _ _).trans ((congrArg (fun k => e₂.hom ≫ k) h₁).trans h₂)

/-- Source transport composition has identity ambient comparisons. -/
def sourceIsoCompIso (C : DenseCompactification f₀) :
    (sourceIso f₁ e₁ h₁ ⋙ sourceIso f₂ e₂ h₂).obj C ≅
      (sourceIso f₂ (e₂ ≪≫ e₁) (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂)).obj C where
  hom :=
    { hom := 𝟙 C.Xbar
      isProper_hom := inferInstanceAs (IsProper (𝟙 C.Xbar))
      open_fac := by
        change (e₂.hom ≫ e₁.hom ≫ C.j) ≫ 𝟙 C.Xbar = (e₂.hom ≫ e₁.hom) ≫ C.j
        simp only [Category.comp_id, Category.assoc]
      base_fac := Category.id_comp _ }
  inv :=
    { hom := 𝟙 C.Xbar
      isProper_hom := inferInstanceAs (IsProper (𝟙 C.Xbar))
      open_fac := by
        change ((e₂.hom ≫ e₁.hom) ≫ C.j) ≫ 𝟙 C.Xbar = e₂.hom ≫ e₁.hom ≫ C.j
        simp only [Category.comp_id, Category.assoc]
      base_fac := Category.id_comp _ }
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- Composition of source transports is naturally identified with the composed isomorphism. -/
def sourceIsoComp : sourceIso f₁ e₁ h₁ ⋙ sourceIso f₂ e₂ h₂ ≅
    sourceIso f₂ (e₂ ≪≫ e₁) (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) :=
  NatIso.ofComponents (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂)
    (fun _ => Subsingleton.elim _ _)

@[simp]
lemma sourceIsoCompIso_hom (C : DenseCompactification f₀) :
    (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).hom.hom = 𝟙 C.Xbar := rfl

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
