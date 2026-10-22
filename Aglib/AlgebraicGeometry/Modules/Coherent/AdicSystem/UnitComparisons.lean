/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Category.Preorder

/-! # Whole diagram comparisons with original unit certificates

All construction and projection laws are proved with abstract categorical
objects, before specializing to quotient sheaves or their ideal powers.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- Lift whole pointwise comparisons to the formal full subcategory, retaining
all original unit equations before specializing quotient sheaves. -/
def formalComparisonOfComponents {C : Type*} [Category C]
    {P : ObjectProperty (ℕᵒᵖ ⥤ C)} (F G : P.FullSubcategory) (U : C)
    (a : ∀ n, U ⟶ F.obj.obj (op n)) (b : ∀ n, U ⟶ G.obj.obj (op n))
    (c : ∀ n, {e : F.obj.obj (op n) ≅ G.obj.obj (op n) // a n ≫ e.hom = b n})
    (h : ∀ {i j} (f : i ⟶ j), F.obj.map f ≫ (c j.unop).val.hom =
      (c i.unop).val.hom ≫ G.obj.map f) :
    {e : F ≅ G // ∀ n, a n ≫ e.hom.hom.app (op n) = b n} :=
  ⟨ObjectProperty.isoMk _ (NatIso.ofComponents (fun j => (c j.unop).val)
    (fun f => h f)), fun j => (c j).property⟩

/-- Pointwise epimorphic original units detect a square of formal diagrams. -/
theorem formalMap_square_of_units {C : Type*} [Category C]
    {P : ObjectProperty (ℕᵒᵖ ⥤ C)} {F₁ F₂ G₁ G₂ : P.FullSubcategory}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) (e₁ : F₁ ⟶ G₁) (e₂ : F₂ ⟶ G₂)
    {U V : C} (u : U ⟶ V)
    (a₁ : ∀ n, U ⟶ F₁.obj.obj (op n)) (a₂ : ∀ n, V ⟶ F₂.obj.obj (op n))
    (b₁ : ∀ n, U ⟶ G₁.obj.obj (op n)) (b₂ : ∀ n, V ⟶ G₂.obj.obj (op n))
    [∀ n, Epi (a₁ n)]
    (ha : ∀ n, a₁ n ≫ f.hom.app (op n) = u ≫ a₂ n)
    (hb : ∀ n, b₁ n ≫ g.hom.app (op n) = u ≫ b₂ n)
    (he₁ : ∀ n, a₁ n ≫ e₁.hom.app (op n) = b₁ n)
    (he₂ : ∀ n, a₂ n ≫ e₂.hom.app (op n) = b₂ n) :
    f ≫ e₂ = e₁ ≫ g := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  change f.hom.app n ≫ e₂.hom.app n = e₁.hom.app n ≫ g.hom.app n
  apply (cancel_epi (a₁ n.unop)).mp
  calc
    a₁ n.unop ≫ (f.hom.app n ≫ e₂.hom.app n) =
        (u ≫ a₂ n.unop) ≫ e₂.hom.app n := by rw [← Category.assoc, ha]
    _ = u ≫ b₂ n.unop := by rw [Category.assoc, he₂]
    _ = b₁ n.unop ≫ g.hom.app n := (hb n.unop).symm
    _ = a₁ n.unop ≫ (e₁.hom.app n ≫ g.hom.app n) := by
      rw [← Category.assoc, he₁]

/-- Forget formal membership only after constructing the whole comparison. -/
def diagramComparisonOfComponents {C : Type*} [Category C]
    (F G : ℕᵒᵖ ⥤ C) (U : C)
    (a : ∀ n, U ⟶ F.obj (op n)) (b : ∀ n, U ⟶ G.obj (op n))
    (c : ∀ n, {e : F.obj (op n) ≅ G.obj (op n) // a n ≫ e.hom = b n})
    (h : ∀ {i j} (f : i ⟶ j), F.map f ≫ (c j.unop).val.hom =
      (c i.unop).val.hom ≫ G.map f) :
    {e : F ≅ G // ∀ n, a n ≫ e.hom.app (op n) = b n} := by
  let P : ObjectProperty (ℕᵒᵖ ⥤ C) := fun _ => True
  let d := formalComparisonOfComponents (P := P) ⟨F, trivial⟩ ⟨G, trivial⟩ U a b c h
  exact ⟨P.ι.mapIso d.val, d.property⟩

/-- The bundle has literally the original native component construction. -/
theorem diagramComparisonOfComponents_val {C : Type*} [Category C]
    (F G : ℕᵒᵖ ⥤ C) (U : C)
    (a : ∀ n, U ⟶ F.obj (op n)) (b : ∀ n, U ⟶ G.obj (op n))
    (c : ∀ n, {e : F.obj (op n) ≅ G.obj (op n) // a n ≫ e.hom = b n})
    (h : ∀ {i j} (f : i ⟶ j), F.map f ≫ (c j.unop).val.hom =
      (c i.unop).val.hom ≫ G.map f) :
    (diagramComparisonOfComponents F G U a b c h).val =
      NatIso.ofComponents (fun j => (c j.unop).val) (fun f => h f) := rfl

/-- Invert a whole native diagram comparison using its original unit law. -/
theorem diagramIso_unit_inv {C : Type*} [Category C] {F G : ℕᵒᵖ ⥤ C}
    (e : F ≅ G) (n : ℕ) {U : C}
    (a : U ⟶ F.obj (op n)) (b : U ⟶ G.obj (op n))
    (h : a ≫ e.hom.app (op n) = b) : b ≫ e.inv.app (op n) = a := by
  rw [← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules.Coherent
