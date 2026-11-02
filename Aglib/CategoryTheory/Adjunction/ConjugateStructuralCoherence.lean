/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.ComparisonCoherence
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Whole structural laws for specified conjugate comparisons

The original adjunctions, left and right comparisons, and their actual
conjugacy equations are inputs. Complete unit and associativity laws transfer
to the specified right comparisons. Equality transport reverses under the
same conjugacy. No additional category realization or endpoint isomorphism
is selected. The localization-unit lemma uses the original localization
factors and the original unit.
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA vA uB vB uC vC uD vD uI

section EqualityTransport

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {I : Sort uI} (L : I → A ⥤ B) (R : I → B ⥤ A) (a : ∀ i, L i ⊣ R i)

/-- Equality of the original indices gives the reversed original right transport. -/
theorem conjugateEquiv_eqToHom_of_family {i j : I} (h : i = j) :
    conjugateEquiv (a j) (a i) (eqToHom (congrArg L h)) =
      eqToHom (congrArg R h.symm) := by
  subst j
  simp

end EqualityTransport

section RightUnit

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {L LT : A ⥤ B} {R RT : B ⥤ A} {I J : B ⥤ B}

/-- The complete right-unit law for left compositors gives the left-unit law
for the specified original right compositors, including its transport. -/
theorem conjugateStructural_right_unit
    (a : L ⊣ R) (i : I ⊣ J) (t : LT ⊣ RT)
    (c : LT ≅ L ⋙ I) (C : RT ≅ J ⋙ R)
    (d : I ≅ 𝟭 B) (D : J ≅ 𝟭 B) (e : LT ≅ L) (E : RT ≅ R)
    (hc : conjugateEquiv (a.comp i) t c.hom = C.inv)
    (hd : conjugateEquiv Adjunction.id i d.hom = D.inv)
    (he : conjugateEquiv a t e.hom = E.inv)
    (h : c ≪≫ Functor.isoWhiskerLeft L d ≪≫ Functor.rightUnitor L = e) :
    C ≪≫ Functor.isoWhiskerRight D R ≪≫ Functor.leftUnitor R = E := by
  have hm : conjugateEquiv a t
      (c.hom ≫ Functor.whiskerLeft L d.hom ≫ (Functor.rightUnitor L).hom) =
      (Functor.leftUnitor R).inv ≫ Functor.whiskerRight D.inv R ≫ C.inv := by
    rw [← conjugateEquiv_comp _ (a.comp i),
      ← conjugateEquiv_comp _ (a.comp Adjunction.id),
      conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft, hd, hc]
    simp only [Category.assoc]
  have hh := congrArg (fun z => conjugateEquiv a t z.hom) h
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom] at hh
  rw [hm, he] at hh
  apply Iso.ext_inv
  simpa only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Category.assoc] using hh

end RightUnit

section LeftUnit

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {L LT : A ⥤ B} {R RT : B ⥤ A} {I J : A ⥤ A}

/-- The complete left-unit law transfers through the actual conjugacy,
reusing the existing normalized-comparison theorem. -/
theorem conjugateStructural_left_unit
    (a : L ⊣ R) (i : I ⊣ J) (t : LT ⊣ RT)
    (c : LT ≅ I ⋙ L) (C : RT ≅ R ⋙ J)
    (d : I ≅ 𝟭 A) (D : J ≅ 𝟭 A) (e : LT ≅ L) (E : RT ≅ R)
    (hc : conjugateEquiv (i.comp a) t c.hom = C.inv)
    (hd : conjugateEquiv Adjunction.id i d.hom = D.inv)
    (he : conjugateEquiv a t e.hom = E.inv)
    (h : c ≪≫ Functor.isoWhiskerRight d L ≪≫ Functor.leftUnitor L = e) :
    C ≪≫ Functor.isoWhiskerLeft R D ≪≫ Functor.rightUnitor R = E := by
  have hm := conjugateEquiv_normalizedComparison t a i c C d D hc hd
  rw [h] at hm
  exact Iso.ext_inv (hm.symm.trans he)

end LeftUnit

section Associativity

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
  {L₃ : C ⥤ D} {R₃ : D ⥤ C}
  {L₁₂ : A ⥤ C} {R₁₂ : C ⥤ A} {L₂₃ : B ⥤ D} {R₂₃ : D ⥤ B}
  {LT LT' : A ⥤ D} {RT RT' : D ⥤ A}

/-- The full associativity equation transfers to the specified right
compositors and the actual reversed transport, without objectwise testing. -/
theorem conjugateStructural_assoc
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (a₁₂ : L₁₂ ⊣ R₁₂) (a₂₃ : L₂₃ ⊣ R₂₃) (aT : LT ⊣ RT) (aT' : LT' ⊣ RT')
    (c₁₂ : L₁₂ ≅ L₁ ⋙ L₂) (c₂₃ : L₂₃ ≅ L₂ ⋙ L₃)
    (c₁₂₃ : LT ≅ L₁ ⋙ L₂₃) (c₁₂₃' : LT' ≅ L₁₂ ⋙ L₃)
    (C₁₂ : R₁₂ ≅ R₂ ⋙ R₁) (C₂₃ : R₂₃ ≅ R₃ ⋙ R₂)
    (C₁₂₃ : RT ≅ R₂₃ ⋙ R₁) (C₁₂₃' : RT' ≅ R₃ ⋙ R₁₂)
    (e : LT ≅ LT') (E : RT' ≅ RT)
    (hc₁₂ : conjugateEquiv (a₁.comp a₂) a₁₂ c₁₂.hom = C₁₂.inv)
    (hc₂₃ : conjugateEquiv (a₂.comp a₃) a₂₃ c₂₃.hom = C₂₃.inv)
    (hc₁₂₃ : conjugateEquiv (a₁.comp a₂₃) aT c₁₂₃.hom = C₁₂₃.inv)
    (hc₁₂₃' : conjugateEquiv (a₁₂.comp a₃) aT' c₁₂₃'.hom = C₁₂₃'.inv)
    (he : conjugateEquiv aT' aT e.hom = E.hom)
    (h : c₁₂₃ ≪≫ Functor.isoWhiskerLeft L₁ c₂₃ =
      e ≪≫ c₁₂₃' ≪≫ Functor.isoWhiskerRight c₁₂ L₃ ≪≫
        Functor.associator L₁ L₂ L₃) :
    C₁₂₃' ≪≫ Functor.isoWhiskerLeft R₃ C₁₂ =
      E ≪≫ C₁₂₃ ≪≫ Functor.isoWhiskerRight C₂₃ R₁ ≪≫
        Functor.associator R₃ R₂ R₁ := by
  have hL : conjugateEquiv (a₁.comp (a₂.comp a₃)) aT
      (c₁₂₃.hom ≫ Functor.whiskerLeft L₁ c₂₃.hom) =
      Functor.whiskerRight C₂₃.inv R₁ ≫ C₁₂₃.inv := by
    rw [← conjugateEquiv_comp _ (a₁.comp a₂₃), conjugateEquiv_whiskerLeft,
      hc₂₃, hc₁₂₃]
  have hR : conjugateEquiv (a₁.comp (a₂.comp a₃)) aT
      (e.hom ≫ c₁₂₃'.hom ≫ Functor.whiskerRight c₁₂.hom L₃ ≫
        (Functor.associator L₁ L₂ L₃).hom) =
      (Functor.associator R₃ R₂ R₁).hom ≫ Functor.whiskerLeft R₃ C₁₂.inv ≫
        C₁₂₃'.inv ≫ E.hom := by
    rw [← conjugateEquiv_comp _ aT', ← conjugateEquiv_comp _ (a₁₂.comp a₃),
      ← conjugateEquiv_comp _ ((a₁.comp a₂).comp a₃),
      conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
      hc₁₂, hc₁₂₃', he]
    all_goals simp only [Category.assoc]
  have hh := congrArg (fun z => conjugateEquiv (a₁.comp (a₂.comp a₃)) aT z.hom) h
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom] at hh
  rw [hL, hR] at hh
  apply Iso.ext_inv
  have hk := congrArg
    (fun z => (Functor.associator R₃ R₂ R₁).inv ≫ z ≫ E.inv) hh
  simpa only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using hk.symm

end Associativity

section StructuralTriangles

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- Invert the complete structural-compositor associativity equation. -/
theorem inverseStructural_assoc
    {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D}
    {FG : A ⥤ C} {GH : B ⥤ D} {T T' : A ⥤ D}
    (cFG : FG ≅ F ⋙ G) (cGH : GH ≅ G ⋙ H)
    (cF : T ≅ F ⋙ GH) (cH : T' ≅ FG ⋙ H) (e : T ≅ T')
    (h : cF ≪≫ Functor.isoWhiskerLeft F cGH =
      e ≪≫ cH ≪≫ Functor.isoWhiskerRight cFG H ≪≫ Functor.associator F G H) :
    Functor.isoWhiskerLeft F cGH.symm ≪≫ cF.symm =
      (Functor.associator F G H).symm ≪≫ Functor.isoWhiskerRight cFG.symm H ≪≫
        cH.symm ≪≫ e.symm := by
  simpa only [Iso.trans_symm, Functor.isoWhiskerLeft_symm,
    Functor.isoWhiskerRight_symm, Iso.trans_assoc] using congrArg Iso.symm h

/-- The actual structural triangle after an invertible compositor is fixed by
the complete unit equation. -/
theorem structuralIso_normalization {X Y Z : D}
    (c : X ≅ Y) (u : Y ≅ Z) (e : X ≅ Z) (h : c ≪≫ u = e) :
    c.symm ≪≫ e = u := by
  rw [← h]
  simp only [Iso.symm_self_id_assoc]

end StructuralTriangles

namespace Adjunction

section Localization

variable {C₁ : Type uA} [Category.{vA} C₁] {C₂ : Type uB} [Category.{vB} C₂]
  {D₁ : Type uC} [Category.{vC} D₁] {D₂ : Type uD} [Category.{vD} D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F)
  (Q₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [Q₁.IsLocalization W₁]
  (Q₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [Q₂.IsLocalization W₂]
  (G' : D₁ ⥤ D₂) (F' : D₂ ⥤ D₁)
  [CatCommSq G Q₁ Q₂ G'] [CatCommSq F Q₂ Q₁ F']

/-- The original invertible unit remains invertible under the actual
localized adjunction, by its original factor equation and essential surjectivity. -/
theorem localization_unit_isIso_of_original [IsIso adj.unit] :
    IsIso (adj.localization Q₁ W₁ Q₂ W₂ G' F').unit := by
  let a := adj.localization Q₁ W₁ Q₂ W₂ G' F'
  have h (X : C₁) : IsIso (a.unit.app (Q₁.obj X)) := by
    dsimp only [a]
    rw [adj.localization_unit_app Q₁ W₁ Q₂ W₂ G' F' X]
    infer_instance
  let : Q₁.EssSurj := Localization.essSurj Q₁ W₁
  have h' (X : D₁) : IsIso (a.unit.app X) := by
    rw [← NatTrans.isIso_app_iff_of_iso _ (Q₁.objObjPreimageIso X)]
    exact h (Q₁.objPreimage X)
  exact NatIso.isIso_of_isIso_app _

end Localization
end Adjunction
end CategoryTheory
