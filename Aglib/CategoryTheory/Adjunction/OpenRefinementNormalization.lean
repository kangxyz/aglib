/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.OpenComparisonPasting
public import Aglib.CategoryTheory.Adjunction.ConjugateStructuralCoherence

/-! # Original source-identity normalization of a left-comparison cube -/

@[expose] public noncomputable section

open CategoryTheory
universe uA vA uB vB uC vC uD vD uE vE uA' vA' uB' vB' uC' vC'

namespace CategoryTheory

/-- Normalize the first original pasting by its actual source-identity comparison. -/
theorem normalize_leftComparison_pasting_first
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    [Category.{vD} D] [Category.{vE} E]
    {J : A ⥤ B} {I : A ⥤ C} {I' : D ⥤ E}
    {F : B ⥤ C} {H : C ⥤ E} {V W : A ⥤ D} {Q : A ⥤ A}
    (d : Q ≅ 𝟭 A) (e : J ⋙ F ≅ Q ⋙ I) (σ : J ⋙ F ≅ I)
    (e' : I ⋙ H ≅ V ⋙ I') (K : A)
    {Z : E} (c : Z ⟶ H.obj (F.obj (J.obj K)))
    (t : Z ⟶ I'.obj (W.obj K)) (g : W.obj K ⟶ V.obj (Q.obj K))
    (δ : W.obj K ⟶ V.obj K)
    (hσ : σ.hom.app K = e.hom.app K ≫ I.map (d.hom.app K))
    (hg : g ≫ V.map (d.hom.app K) = δ)
    (hp : c ≫ H.map (e.hom.app K) ≫ e'.hom.app (Q.obj K) = t ≫ I'.map g) :
    c ≫ H.map (σ.hom.app K) ≫ e'.hom.app K = t ≫ I'.map δ := by
  rw [hσ, H.map_comp]
  simp only [Category.assoc]
  have hn := e'.hom.naturality (d.hom.app K)
  change H.map (I.map (d.hom.app K)) ≫ e'.hom.app K =
    e'.hom.app (Q.obj K) ≫ I'.map (V.map (d.hom.app K)) at hn
  rw [hn, reassoc_of% hp]
  simp only [← I'.map_comp, hg]

/-- Normalize the second original pasting by its actual source-identity comparison. -/
theorem normalize_leftComparison_pasting_second
    {A : Type uA} {B : Type uB} {C : Type uC} [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    {J : A ⥤ B} {I : A ⥤ C} {F : B ⥤ C} {Q : A ⥤ A}
    (d : Q ≅ 𝟭 A) (e : J ⋙ F ≅ Q ⋙ I) (σ : J ⋙ F ≅ I) (K : A)
    {Z : C} (c : Z ⟶ F.obj (J.obj K))
    {K₀ : A} (t : Z ⟶ I.obj K₀) (g : K₀ ⟶ Q.obj K) (δ : K₀ ⟶ K)
    (hσ : σ.hom.app K = e.hom.app K ≫ I.map (d.hom.app K))
    (hg : g ≫ d.hom.app K = δ)
    (hp : c ≫ e.hom.app K = t ≫ I.map g) : c ≫ σ.hom.app K = t ≫ I.map δ := by
  rw [hσ, ← Category.assoc, hp]
  simp only [Category.assoc, ← I.map_comp, hg]

private theorem comparison_cube_from_pastings
    {C : Type uC} [Category.{vC} C] {A B D E F : C}
    (c₁ : A ≅ B) (c₂ : D ≅ E) (t : D ≅ A)
    (l : B ⟶ F) (r : E ⟶ F) (p : A ⟶ F) (q : D ⟶ F)
    (hl : c₁.hom ≫ l = p) (hr : c₂.hom ≫ r = q) (ht : t.hom ≫ p = q) :
    (c₂.inv ≫ t.hom ≫ c₁.hom) ≫ l = r := by
  rw [Category.assoc, Category.assoc, hl, ht, ← hr]
  simp


/-- Whole first-path normalized pasting proposition. -/
def LeftFirstPastingEquation
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    [Category.{vD} D] [Category.{vE} E]
    {J : A ⥤ B} {I : A ⥤ C} {I' : D ⥤ E}
    {L : B ⥤ C} {H : C ⥤ E} {V : A ⥤ D} {F : B ⥤ E}
    (c : F ≅ L ⋙ H) (σ : J ⋙ L ≅ I) (e : I ⋙ H ≅ V ⋙ I')
    (p : J ⋙ F ≅ V ⋙ I') : Prop :=
  ∀ K, c.hom.app (J.obj K) ≫ H.map (σ.hom.app K) ≫ e.hom.app K = p.hom.app K

/-- Whole second-path normalized pasting proposition. -/
def LeftSecondPastingEquation
    {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'} {C' : Type uC'}
    [Category.{vA} A] [Category.{vB} B]
    [Category.{vA'} A'] [Category.{vB'} B'] [Category.{vC'} C']
    {J : A ⥤ B} {J' : A' ⥤ B'} {I' : A' ⥤ C'}
    {G : B ⥤ B'} {L' : B' ⥤ C'} {V : A ⥤ A'} {F : B ⥤ C'}
    (c : F ≅ G ⋙ L') (e : J ⋙ G ≅ V ⋙ J') (σ : J' ⋙ L' ≅ I')
    (p : J ⋙ F ≅ V ⋙ I') : Prop :=
  ∀ K, c.hom.app (J.obj K) ≫ L'.map (e.hom.app K) ≫ σ.hom.app (V.obj K) = p.hom.app K

/-- Whole comparison transport proposition for specified total functors. -/
def LeftTotalTransportEquation
    {A : Type uA} {B : Type uB} {D : Type uD} {E : Type uE}
    [Category.{vA} A] [Category.{vB} B] [Category.{vD} D] [Category.{vE} E]
    {J : A ⥤ B} {I : D ⥤ E} {V : A ⥤ D} {F₀ F₁ : B ⥤ E}
    (t : F₀ ≅ F₁) (p : J ⋙ F₁ ≅ V ⋙ I) (q : J ⋙ F₀ ≅ V ⋙ I) : Prop :=
  ∀ K, t.hom.app (J.obj K) ≫ p.hom.app K = q.hom.app K


/-- Whole original left-comparison cube equation, before concrete models are installed. -/
def LeftRefinementCubeEquation
    {A : Type uA} {B : Type uB} {C : Type uC} {A' : Type uA'} {B' : Type uB'} {C' : Type uC'}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    [Category.{vA'} A'] [Category.{vB'} B'] [Category.{vC'} C']
    {J : A ⥤ B} {I : A ⥤ C} {J' : A' ⥤ B'} {I' : A' ⥤ C'}
    {L : B ⥤ C} {L' : B' ⥤ C'} {G : B ⥤ B'} {H : C ⥤ C'} {V : A ⥤ A'}
    (α : G ⋙ L' ≅ L ⋙ H) (σ : J ⋙ L ≅ I) (σ' : J' ⋙ L' ≅ I')
    (eD : J ⋙ G ≅ V ⋙ J') (eC : I ⋙ H ≅ V ⋙ I') : Prop :=
  ∀ K, α.hom.app (J.obj K) ≫ H.map (σ.hom.app K) ≫ eC.hom.app K =
    L'.map (eD.hom.app K) ≫ σ'.hom.app (V.obj K)

/-- Two original pasting laws and actual arrow transport give the refinement cube. -/
theorem leftRefinementCube_of_pastings
    {A : Type uA} {B : Type uB} {C : Type uC} {A' : Type uA'} {B' : Type uB'} {C' : Type uC'}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    [Category.{vA'} A'] [Category.{vB'} B'] [Category.{vC'} C']
    {J : A ⥤ B} {I : A ⥤ C} {J' : A' ⥤ B'} {I' : A' ⥤ C'}
    {L : B ⥤ C} {L' : B' ⥤ C'} {G : B ⥤ B'} {H : C ⥤ C'} {V : A ⥤ A'}
    {F₁ F₂ : B ⥤ C'}
    (α : G ⋙ L' ≅ L ⋙ H) (σ : J ⋙ L ≅ I) (σ' : J' ⋙ L' ≅ I')
    (eD : J ⋙ G ≅ V ⋙ J') (eC : I ⋙ H ≅ V ⋙ I')
    (c₁ : F₁ ≅ L ⋙ H) (c₂ : F₂ ≅ G ⋙ L') (t : F₂ ≅ F₁)
    (p : J ⋙ F₁ ≅ V ⋙ I') (q : J ⋙ F₂ ≅ V ⋙ I')
    (hα : α = c₂.symm ≪≫ t ≪≫ c₁)
    (h₁ : LeftFirstPastingEquation c₁ σ eC p)
    (h₂ : LeftSecondPastingEquation c₂ eD σ' q)
    (ht : LeftTotalTransportEquation t p q) :
    LeftRefinementCubeEquation α σ σ' eD eC := by
  intro K
  rw [hα]
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.app_hom,
    Iso.app_inv, Category.assoc] using comparison_cube_from_pastings
      (c₁.app (J.obj K)) (c₂.app (J.obj K)) (t.app (J.obj K)) _ _ _ _
      (h₁ K) (h₂ K) (ht K)


/-- Two original unit laws normalize the specified source-square factors. -/
theorem sourceSquareIso_unit_normalization
    {C : Type uC} [Category.{vC} C] {A B D E T : C}
    (a : A ≅ B) (b : D ≅ E) (l : B ≅ T) (r : E ≅ T)
    (eA : A = T) (eD : D = T) (eAD : A = D)
    (hA : a ≪≫ l = eqToIso eA) (hD : b ≪≫ r = eqToIso eD) :
    (a.symm ≪≫ eqToIso eAD ≪≫ b) ≪≫ r = l := by
  calc
    _ = a.symm ≪≫ (eqToIso eAD ≪≫ eqToIso eD) := by
      simp only [Iso.trans_assoc, hD]
    _ = a.symm ≪≫ eqToIso eA := by simp only [eqToIso_trans]
    _ = l := structuralIso_normalization a l (eqToIso eA) hA

/-- Evaluate the whole original horizontal identity normalization once, abstractly. -/
theorem originalSquare_identity_component
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B] {L : A ⥤ B}
    {I : A ⥤ A} {J : B ⥤ B}
    (α : I ⋙ L ≅ L ⋙ J) (dI : I ≅ 𝟭 A) (dJ : J ≅ 𝟭 B)
    (h : α ≪≫ Functor.isoWhiskerLeft L dJ ≪≫ Functor.rightUnitor L =
      Functor.isoWhiskerRight dI L ≪≫ Functor.leftUnitor L) (X : A) :
    α.hom.app X ≫ dJ.hom.app (L.obj X) = L.map (dI.hom.app X) := by
  have he := congrArg (fun i => i.hom.app X) h
  change α.hom.app X ≫ dJ.hom.app (L.obj X) ≫ 𝟙 _ =
    L.map (dI.hom.app X) ≫ 𝟙 _ at he
  simpa only [Category.comp_id] using he

/-- The actual adjunction mate retains the original horizontal identity maps. -/
theorem originalMate_horizontal_identity
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B] {L : A ⥤ B} {R : B ⥤ A}
    {I : A ⥤ A} {J : B ⥤ B} (adj : L ⊣ R)
    (α : I ⋙ L ≅ L ⋙ J) (dI : I ≅ 𝟭 A) (dJ : J ≅ 𝟭 B)
    (β : R ⋙ I ⟶ J ⋙ R)
    (hβ : β = (mateEquiv adj adj (TwoSquare.mk I L L J α.hom)).natTrans)
    (h : α ≪≫ Functor.isoWhiskerLeft L dJ ≪≫ Functor.rightUnitor L =
      Functor.isoWhiskerRight dI L ≪≫ Functor.leftUnitor L) (X : B) :
    β.app X ≫ R.map (dJ.hom.app X) = dI.hom.app (R.obj X) := by
  have hα : ∀ Y, L.map (dI.hom.app Y) ≫ (TwoSquare.hId L).app Y =
      α.hom.app Y ≫ dJ.hom.app (L.obj Y) := by
    intro Y
    rw [TwoSquare.hId_app]
    exact (Category.comp_id (L.map (dI.hom.app Y))).trans
      (originalSquare_identity_component α dI dJ h Y).symm
  have he := mateEquiv_top_bottom_naturality adj adj
    (TwoSquare.mk I L L J α.hom) (TwoSquare.hId L) dI.hom dJ.hom hα X
  rw [hβ]
  simpa [mateEquiv_hId, TwoSquare.vId] using he.symm

/-- The original transpose retains the vertical identity normalization. -/
theorem originalSquare_transpose_identity
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B] {L : A ⥤ B}
    {I : A ⥤ A} {J : B ⥤ B}
    (α : I ⋙ L ≅ L ⋙ J) (α' : L ⋙ J ≅ I ⋙ L)
    (dI : I ≅ 𝟭 A) (dJ : J ≅ 𝟭 B) (hα' : α' = α.symm)
    (h : α ≪≫ Functor.isoWhiskerLeft L dJ ≪≫ Functor.rightUnitor L =
      Functor.isoWhiskerRight dI L ≪≫ Functor.leftUnitor L) (X : A) :
    dJ.hom.app (L.obj X) = α'.hom.app X ≫ L.map (dI.hom.app X) := by
  rw [hα', Iso.symm_hom, ← originalSquare_identity_component α dI dJ h X,
    Iso.inv_hom_id_app_assoc]

end CategoryTheory
