/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.OpenCompositionPost

/-! # Reflect original binary-composition equations through a faithful target inclusion -/

@[expose] public section
namespace CategoryTheory
variable {A B C D E : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
  {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D}
  {M : A ⥤ C} {N : B ⥤ D} {P P' : A ⥤ D}

/-- The original component maps after inclusion, with no inverse normalization. -/
def FaithfulCompositionEquation (U : D ⥤ E)
    (a : F ⋙ G ≅ M) (b : M ⋙ H ≅ P)
    (c : F ⋙ N ≅ P') (d : G ⋙ H ≅ N) (e : P' ≅ P) : Prop :=
  ∀ X, U.map (H.map (a.hom.app X)) ≫ U.map (b.hom.app X) =
    U.map (d.hom.app (F.obj X)) ≫ U.map (c.hom.app X) ≫ U.map (e.hom.app X)

/-- Faithfulness reflects the actual original map equation. -/
theorem openCompositionPostEquation_of_faithful (U : D ⥤ E) [U.Faithful]
    (a : F ⋙ G ≅ M) (b : M ⋙ H ≅ P)
    (c : F ⋙ N ≅ P') (d : G ⋙ H ≅ N) (e : P' ≅ P)
    (h : FaithfulCompositionEquation U a b c d e) :
    OpenCompositionPostEquation a b c d e := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply U.map_injective
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Functor.map_comp] using h X

variable {S M₀ N₀ P₀ T : E}

/-- Substitute only already proved formulas for the five original component morphisms. -/
theorem compositionEquation_of_formulas
    (a a' : S ⟶ M₀) (b b' : M₀ ⟶ T)
    (c c' : S ⟶ N₀) (d d' : N₀ ⟶ P₀) (e e' : P₀ ⟶ T)
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') (he : e = e')
    (h : a' ≫ b' = c' ≫ d' ≫ e') : a ≫ b = c ≫ d ≫ e := by
  subst a'
  subst b'
  subst c'
  subst d'
  subst e'
  exact h

end CategoryTheory
