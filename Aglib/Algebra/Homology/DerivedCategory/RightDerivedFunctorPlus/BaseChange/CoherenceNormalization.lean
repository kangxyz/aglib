/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CoherenceChain

/-!
# Normalization of actual exchange squares

The actual component isomorphisms remain parameters. Their canonical
factorizations and the comparison chain imply horizontal square coherence;
all unfolding and cancellation take place before geometric specialization.
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : D ⥤ C)
  {X Y Z U V W Q : C} {A B C₀ D₀ : D}
  (p : Z ≅ X) (b : U ≅ Y) (t : U ≅ V) (c : V ≅ F.obj A)
  (d : B ≅ A) (r : B ≅ C₀) (e : C₀ ≅ D₀)
  (τ : Z ≅ W) (u : W ≅ Q) (q : X ⟶ Y) (v : Q ⟶ F.obj D₀)
  (α₁ : A ≅ D₀) (α₂ : Y ≅ F.obj A) (α : X ≅ Q)

/-- An exchange chain gives the actual composite square using named iso witnesses. -/
theorem exchangeCoherence_normalize
    (h₁ : α₁ = d.symm ≪≫ r ≪≫ e)
    (h₂ : α₂ = b.symm ≪≫ t ≪≫ c)
    (h : α = p.symm ≪≫ τ ≪≫ u)
    (hc : p.hom ≫ q ≫ b.inv ≫ t.hom ≫ c.hom ≫
        F.map d.inv ≫ F.map r.hom ≫ F.map e.hom = τ.hom ≫ u.hom ≫ v) :
    q ≫ α₂.hom ≫ F.map α₁.hom = α.hom ≫ v := by
  subst α₁
  subst α₂
  subst α
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  exact (Iso.eq_inv_comp p).mpr hc

/-- A named factorization of the whole natural iso gives its component factorization. -/
theorem exchangeCoherence_app_decomposition
    {C D : Type*} [Category* C] [Category* D]
    {F₀ F₁ F₂ F₃ : C ⥤ D}
    (α : F₁ ≅ F₃) (a : F₀ ≅ F₁) (t : F₀ ≅ F₂) (c : F₂ ≅ F₃)
    (hα : α = a.symm ≪≫ t ≪≫ c) (X : C) :
    α.app X = (a.app X).symm ≪≫ t.app X ≪≫ c.app X := by
  subst α
  rfl

/-- The whole natural-iso factorization gives a raw-arrow square at each object. -/
theorem exchangeCoherence_square_app
    {C D : Type*} [Category* C] [Category* D]
    {F₀ F₁ F₂ F₃ : C ⥤ D}
    (α : F₁ ≅ F₃) (a : F₀ ≅ F₁) (t : F₀ ≅ F₂) (c : F₂ ≅ F₃)
    (hα : α = a.symm ≪≫ t ≪≫ c) (X : C) :
    a.hom.app X ≫ α.hom.app X = t.hom.app X ≫ c.hom.app X := by
  subst α
  change a.hom.app X ≫ (a.inv.app X ≫ (t.hom.app X ≫ c.hom.app X)) = _
  exact Iso.hom_inv_id_app_assoc a X _

end CategoryTheory
