/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import Aglib.CategoryTheory.Adjunction.MixedMateNormalization
public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-! # Mixed mates preserve the canonical map between the outer adjoints

The comparison is Mathlib's existing `Adjunction.Triple.leftToRight`. Its two
units are retained. The right comparison is the native mate of the original
right exchange, not an arbitrarily chosen commuting-image isomorphism.
-/

@[expose] public noncomputable section
namespace CategoryTheory.Adjunction
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {J : A ⥤ B} {Q : B ⥤ A} {S : A ⥤ B}
  {J' : C ⥤ D} {Q' : D ⥤ C} {S' : C ⥤ D}
  {R : D ⥤ B} {R' : C ⥤ A}
  (t : Triple J Q S) (t' : Triple J' Q' S')
  [J.Full] [J.Faithful] [J'.Full] [J'.Faithful]
  (β : R ⋙ Q ≅ Q' ⋙ R') (σ : R' ⋙ J ⟶ J' ⋙ R)

/-- The original transpose equation, before inserting the outer-adjoint comparison. -/
def TripleMateTransposeEquation : Prop :=
  ∀ K, t.adj₁.unit.app (R'.obj K) ≫ Q.map (σ.app K) =
    R'.map (t'.adj₁.unit.app K) ≫ β.inv.app (J'.obj K)

omit [J.Full] [J.Faithful] [J'.Full] [J'.Faithful] in
/-- Original conjugacy supplies the transpose equation for the unchanged mixed mate. -/
theorem tripleMateTransposeEquation {P : B ⥤ D} {P' : A ⥤ C}
    (aP : P ⊣ R) (aP' : P' ⊣ R') (α : J ⋙ P ⟶ P' ⋙ J')
    (h : conjugateEquiv (aP'.comp t'.adj₁) (t.adj₁.comp aP) α = β.inv) :
    TripleMateTransposeEquation t t' β
      (mateEquiv aP' aP (TwoSquare.mk _ _ _ _ α)).natTrans := by
  intro K
  simpa only [Adjunction.homEquiv_apply, mateEquiv_app_eq] using
    mixedMate_homEquiv t.adj₁ t'.adj₁ aP aP' α β h K

/-- Whole original compatibility of the canonical outer-adjoint maps and the two mates. -/
def TripleMateCompatibilityEquation : Prop :=
  ∀ K, σ.app K ≫ R.map (t'.leftToRight.app K) ≫
      (mateEquiv t'.adj₂ t.adj₂ (TwoSquare.mk _ _ _ _ β.hom)).app K =
    t.leftToRight.app (R'.obj K)

/-- The canonical outer-adjoint maps commute with the original mixed and right mates. -/
theorem leftToRight_mate_compatibility
    (hσ : TripleMateTransposeEquation t t' β σ) (K : C) :
    σ.app K ≫ R.map (t'.leftToRight.app K) ≫
        (mateEquiv t'.adj₂ t.adj₂ (TwoSquare.mk _ _ _ _ β.hom)).app K =
      t.leftToRight.app (R'.obj K) := by
  let γ := (mateEquiv t'.adj₂ t.adj₂ (TwoSquare.mk _ _ _ _ β.hom)).natTrans
  have hm := unit_mateEquiv t'.adj₂ t.adj₂
    (TwoSquare.mk _ _ _ _ β.hom) (J'.obj K)
  have hn := γ.naturality (inv (t'.adj₁.unit.app K))
  change R.map (t'.adj₂.unit.app (J'.obj K)) ≫ γ.app (Q'.obj (J'.obj K)) =
    t.adj₂.unit.app (R.obj (J'.obj K)) ≫ S.map (β.hom.app (J'.obj K)) at hm
  change R.map (S'.map (inv (t'.adj₁.unit.app K))) ≫ γ.app K =
    γ.app (Q'.obj (J'.obj K)) ≫ S.map (R'.map (inv (t'.adj₁.unit.app K))) at hn
  have hu := t.adj₂.unit_naturality (σ.app K)
  have ht : Q.map (σ.app K) ≫ β.hom.app (J'.obj K) ≫
      R'.map (inv (t'.adj₁.unit.app K)) = inv (t.adj₁.unit.app (R'.obj K)) := by
    apply (cancel_epi (t.adj₁.unit.app (R'.obj K))).mp
    rw [← Category.assoc, ← Category.assoc, hσ]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← R'.map_comp, IsIso.hom_inv_id, R'.map_id, IsIso.hom_inv_id]
    rfl
  rw [Triple.leftToRight_app, Triple.leftToRight_app, ← S'.map_inv, ← S.map_inv,
    R.map_comp]
  change σ.app K ≫ (R.map (t'.adj₂.unit.app (J'.obj K)) ≫
    R.map (S'.map (inv (t'.adj₁.unit.app K)))) ≫ γ.app K = _
  calc
    _ = σ.app K ≫ R.map (t'.adj₂.unit.app (J'.obj K)) ≫
        (R.map (S'.map (inv (t'.adj₁.unit.app K))) ≫ γ.app K) := by
      simp only [Category.assoc]
    _ = σ.app K ≫ R.map (t'.adj₂.unit.app (J'.obj K)) ≫
        (γ.app (Q'.obj (J'.obj K)) ≫
          S.map (R'.map (inv (t'.adj₁.unit.app K)))) := by
      exact congrArg (fun z => σ.app K ≫ R.map (t'.adj₂.unit.app (J'.obj K)) ≫ z) hn
    _ = σ.app K ≫ (t.adj₂.unit.app (R.obj (J'.obj K)) ≫
        S.map (β.hom.app (J'.obj K))) ≫
          S.map (R'.map (inv (t'.adj₁.unit.app K))) := by
      simpa only [Category.assoc] using
        congrArg (fun z => σ.app K ≫ z ≫ S.map (R'.map (inv (t'.adj₁.unit.app K)))) hm
    _ = t.adj₂.unit.app (J.obj (R'.obj K)) ≫
        S.map (Q.map (σ.app K) ≫ β.hom.app (J'.obj K) ≫
          R'.map (inv (t'.adj₁.unit.app K))) := by
      rw [S.map_comp, S.map_comp]
      simpa only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj,
        Category.assoc] using
        congrArg (fun z => z ≫ S.map (β.hom.app (J'.obj K)) ≫
          S.map (R'.map (inv (t'.adj₁.unit.app K)))) hu.symm
    _ = _ := by rw [ht]

/-- The compatibility equation before any concrete derived model is substituted. -/
theorem tripleMateCompatibilityEquation
    (hσ : TripleMateTransposeEquation t t' β σ) :
    TripleMateCompatibilityEquation t t' β σ :=
  leftToRight_mate_compatibility t t' β σ hσ

end CategoryTheory.Adjunction
