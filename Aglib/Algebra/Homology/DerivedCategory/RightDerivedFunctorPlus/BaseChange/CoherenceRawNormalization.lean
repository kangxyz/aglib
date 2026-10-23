/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CoherenceChain

/-!
# Raw-arrow normalization of actual exchange squares

Canonical component arrows remain opaque. Their original square equations and
comparison inverse laws normalize the comparison chain without constructing
pointwise isomorphism structures at the geometric specialization.
-/

@[expose] public section

namespace CategoryTheory

/-- Normalize actual component arrows using only raw square and inverse equations. -/
theorem exchangeCoherence_normalize_arrows
    {C D : Type*} [Category* C] [Category* D] (F : D ⥤ C)
    {X Y Z U V W Q : C} {A B C₀ D₀ : D}
    (p : Z ⟶ X) (pi : X ⟶ Z) (b : U ⟶ Y) (bi : Y ⟶ U)
    (t : U ⟶ V) (c : V ⟶ F.obj A)
    (d : B ⟶ A) (di : A ⟶ B) (r : B ⟶ C₀) (e : C₀ ⟶ D₀)
    (τ : Z ⟶ W) (u : W ⟶ Q) (q : X ⟶ Y) (v : Q ⟶ F.obj D₀)
    (s₁ : A ⟶ D₀) (s₂ : Y ⟶ F.obj A) (s : X ⟶ Q)
    (hp : pi ≫ p = 𝟙 X) (hb : bi ≫ b = 𝟙 Y) (hd : di ≫ d = 𝟙 A)
    (h₁ : d ≫ s₁ = r ≫ e) (h₂ : b ≫ s₂ = t ≫ c) (h : p ≫ s = τ ≫ u)
    (hc : p ≫ q ≫ bi ≫ t ≫ c ≫ F.map di ≫ F.map r ≫ F.map e =
      τ ≫ u ≫ v) :
    q ≫ s₂ ≫ F.map s₁ = s ≫ v := by
  rw [← F.map_comp r e, ← h₁, F.map_comp d s₁] at hc
  rw [← CategoryTheory.Functor.map_comp_assoc, hd,
    CategoryTheory.Functor.map_id, Category.id_comp] at hc
  rw [← reassoc_of% h₂, reassoc_of% hb, ← reassoc_of% h] at hc
  have hc' := congrArg (fun k => pi ≫ k) hc
  simpa only [← Category.assoc, hp, Category.id_comp] using hc'

/-- Rotate a comparison equation using only its primitive inverse witnesses. -/
theorem exchangeCoherence_rotate_start
    {C : Type*} [Category* C] {A B D E F : C}
    (a : A ⟶ B) (ai : B ⟶ A) (p : B ⟶ D) (q : D ⟶ E)
    (m : A ⟶ F) (b : F ⟶ E) (bi : E ⟶ F)
    (ha : ai ≫ a = 𝟙 B) (hb : b ≫ bi = 𝟙 F)
    (h : a ≫ p ≫ q = m ≫ b) :
    p ≫ q ≫ bi = ai ≫ m := by
  have hc := congrArg (fun z => ai ≫ z ≫ bi) h
  simpa only [Category.assoc, reassoc_of% ha, hb, Category.id_comp,
    Category.comp_id] using hc

/-- Rotate the terminal comparison using a primitive inverse witness. -/
theorem exchangeCoherence_rotate_finish
    {C : Type*} [Category* C] {A B D : C}
    (a : A ⟶ B) (ai : B ⟶ A) (p : B ⟶ D) (q : A ⟶ D)
    (ha : ai ≫ a = 𝟙 B) (h : a ≫ p = q) :
    p = ai ≫ q := by
  have hc := congrArg (fun z => ai ≫ z) h
  simpa only [← Category.assoc, ha, Category.id_comp] using hc

/-- Functors preserve a specified inverse equation without constructing a mapped iso. -/
theorem exchangeCoherence_map_inverse
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y : C} (d : X ⟶ Y) (di : Y ⟶ X) (hd : d ≫ di = 𝟙 X) :
    F.map d ≫ F.map di = 𝟙 (F.obj X) := by
  rw [← F.map_comp, hd, F.map_id]

/-- The comparison chase with primitive arrows and a specified inverse equation. -/
theorem exchangeCoherence_chain_arrows
    {C : Type*} [Category* C]
    {A B C₀ D E F G H I J K L M N O : C}
    {p : A ⟶ B} {q : B ⟶ C₀} {b₀ : C₀ ⟶ D} {t₂ : D ⟶ E}
    {c₀ : E ⟶ F} (d : G ⟶ F) (di : F ⟶ G)
    {t₁ : G ⟶ H} {e₀ : H ⟶ I}
    {a : A ⟶ J} {m : J ⟶ D} {b : J ⟶ K} {n : K ⟶ E}
    {c : K ⟶ L} {r : L ⟶ G} {e : L ⟶ M} {s : M ⟶ H}
    {z : M ⟶ N} {u : N ⟶ O} {v : O ⟶ I} {τ : A ⟶ N}
    (hd : d ≫ di = 𝟙 G)
    (h₁ : p ≫ q ≫ b₀ = a ≫ m)
    (h₂ : m ≫ t₂ = b ≫ n)
    (h₃ : n ≫ c₀ = c ≫ r ≫ d)
    (h₄ : r ≫ t₁ = e ≫ s)
    (h₅ : s ≫ e₀ = z ≫ u ≫ v)
    (ht : a ≫ b ≫ c ≫ e ≫ z = τ) :
    p ≫ q ≫ b₀ ≫ t₂ ≫ c₀ ≫ di ≫ t₁ ≫ e₀ = τ ≫ u ≫ v := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]
  simp only [reassoc_of% hd]
  rw [reassoc_of% h₄, h₅]
  rw [reassoc_of% ht]

/-- A functor-valued comparison chase closes equality transport before specialization.
The six source indices carry only actual equalities; the closing pentagon is proved,
not supplied as an additional coherence hypothesis. -/
theorem exchangeCoherence_chain_natTransport
    {I C D : Type*} [Category* C] [Category* D]
    (P : I → C ⥤ D) (A : C) {x₀ x₁ x₂ x₃ x₄ x₅ : I}
    (e₁₀ : x₁ = x₀) (e₁₂ : x₁ = x₂) (e₂₃ : x₂ = x₃)
    (e₃₄ : x₃ = x₄) (e₅₄ : x₅ = x₄) (e₀₅ : x₀ = x₅)
    {B₀ C₀ D₀ E₀ F₀ G₀ H₀ I₀ O₀ : D}
    {p : (P x₀).obj A ⟶ B₀} {q : B₀ ⟶ C₀} {b₀ : C₀ ⟶ D₀}
    {t₂ : D₀ ⟶ E₀} {c₀ : E₀ ⟶ F₀} (d : G₀ ⟶ F₀) (di : F₀ ⟶ G₀)
    {t₁ : G₀ ⟶ H₀} {e₀ : H₀ ⟶ I₀}
    {m : (P x₁).obj A ⟶ D₀} {n : (P x₂).obj A ⟶ E₀}
    {r : (P x₃).obj A ⟶ G₀} {s : (P x₄).obj A ⟶ H₀}
    {u : (P x₅).obj A ⟶ O₀} {v : O₀ ⟶ I₀}
    (hd : d ≫ di = 𝟙 G₀)
    (h₁ : p ≫ q ≫ b₀ = (eqToIso (congrArg P e₁₀)).inv.app A ≫ m)
    (h₂ : m ≫ t₂ = (eqToIso (congrArg P e₁₂)).hom.app A ≫ n)
    (h₃ : n ≫ c₀ = (eqToIso (congrArg P e₂₃)).hom.app A ≫ r ≫ d)
    (h₄ : r ≫ t₁ = (eqToIso (congrArg P e₃₄)).hom.app A ≫ s)
    (h₅ : s ≫ e₀ = (eqToIso (congrArg P e₅₄)).inv.app A ≫ u ≫ v) :
    p ≫ q ≫ b₀ ≫ t₂ ≫ c₀ ≫ di ≫ t₁ ≫ e₀ =
      (eqToIso (congrArg P e₀₅)).hom.app A ≫ u ≫ v := by
  refine exchangeCoherence_chain_arrows d di hd h₁ h₂ h₃ h₄ h₅ ?_
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_trans]

end CategoryTheory
