/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCartesianComposition
public import Aglib.CategoryTheory.Functor.OpenCompositionPost

/-! # Whole original Cartesian map equations yield the same isomorphism associativity

All five maps are supplied unchanged. Their identities with the specified
isomorphisms are consumed abstractly, before any native derived functor is exposed.
-/

@[expose] public section
namespace CategoryTheory
/-- A regular boundary retaining the original isomorphism and its original map. -/
def OriginalIsoHomFormula {A B : Type*} [Category* A] [Category* B]
    {F G : A ⥤ B} (a : F ≅ G) (α : F ⟶ G) : Prop := ∀ K, a.hom.app K = α.app K

/-- Package a proved original map equality without changing either map. -/
theorem originalIsoHomFormula_of_hom_eq {A B : Type*} [Category* A] [Category* B]
    {F G : A ⥤ B} (a : F ≅ G) (α : F ⟶ G) (h : a.hom = α) :
    OriginalIsoHomFormula a α := by
  intro K
  exact congrArg (fun t => t.app K) h

section General
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D}
  {M : A ⥤ C} {N : B ⥤ D} {P P' : A ⥤ D}

/-- Whole original homomorphism identities, not componentwise native unfolding,
transport the actual postcomposition equation to the specified isomorphisms. -/
theorem imageCompositionIso_of_homEquation
    (a : F ⋙ G ≅ M) (b : M ⋙ H ≅ P) (c : F ⋙ N ≅ P')
    (d : G ⋙ H ≅ N) (e : P' ≅ P)
    (α : F ⋙ G ⟶ M) (β : M ⋙ H ⟶ P) (γ : F ⋙ N ⟶ P')
    (δ : G ⋙ H ⟶ N) (ε : P' ⟶ P)
    (ha : a.hom = α) (hb : b.hom = β) (hc : c.hom = γ)
    (hd : d.hom = δ) (he : e.hom = ε)
    (h : Functor.whiskerRight α H ≫ β = Functor.whiskerLeft F δ ≫ γ ≫ ε) :
    OpenCompositionEquation a (b ≪≫ e.symm) c d := by
  apply openCompositionEquation_of_post a b c d e
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hk := congrArg (fun t => t.app K) h
  simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, ha, hb, hc, hd, he] using hk
end General

section Cartesian
variable {D A₀ A₁ A₂ B₀ B₁ Y Z C E : Type*}
  [Category* D] [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* B₀] [Category* B₁] [Category* Y] [Category* Z] [Category* C] [Category* E]
  {K : D ⥤ A₀} {J₁ : D ⥤ A₁} {J₂ : D ⥤ A₂}
  {Q₀ : A₀ ⥤ Y} {I₁ : Y ⥤ B₀} {Q₁ : B₀ ⥤ Z}
  {Vsrc : A₁ ⥤ Z} {I₂ : Z ⥤ C} {P : C ⥤ E}
  {Hsrc : Y ⥤ B₁} {Stail : B₁ ⥤ E} {S Sright : A₂ ⥤ E}

/-- Preserve the original regular Cartesian equation as one whole proof argument. -/
theorem imageCartesianCompositionIso
    (a : (K ⋙ Q₀) ⋙ (I₁ ⋙ Q₁) ≅ J₁ ⋙ Vsrc)
    (b : (J₁ ⋙ Vsrc) ⋙ (I₂ ⋙ P) ≅ J₂ ⋙ S)
    (c : (K ⋙ Q₀) ⋙ (Hsrc ⋙ Stail) ≅ J₂ ⋙ Sright)
    (d : (I₁ ⋙ Q₁) ⋙ (I₂ ⋙ P) ≅ Hsrc ⋙ Stail)
    (e : J₂ ⋙ Sright ≅ J₂ ⋙ S) (ep : Sright ≅ S)
    (α : K ⋙ Q₀ ⋙ I₁ ⋙ Q₁ ⟶ J₁ ⋙ Vsrc)
    (β : J₁ ⋙ Vsrc ⋙ I₂ ⋙ P ⟶ J₂ ⋙ S)
    (γ : K ⋙ Q₀ ⋙ Hsrc ⋙ Stail ⟶ J₂ ⋙ Sright)
    (δ : I₁ ⋙ Q₁ ⋙ I₂ ⋙ P ⟶ Hsrc ⋙ Stail)
    (ha : a.hom = α) (hb : b.hom = β) (hc : c.hom = γ)
    (hd : d.hom = δ) (he : e.hom = Functor.whiskerLeft J₂ ep.hom)
    (h : ImageCartesianCompositionEquation ep α β δ γ) :
    OpenCompositionEquation a (b ≪≫ e.symm) c d :=
  imageCompositionIso_of_homEquation a b c d e α β γ δ
    (Functor.whiskerLeft J₂ ep.hom) ha hb hc hd he h
/-- Consume regular original formula boundaries before exposing native functors. -/
theorem imageCartesianCompositionIso_of_formulas
    (a : (K ⋙ Q₀) ⋙ (I₁ ⋙ Q₁) ≅ J₁ ⋙ Vsrc)
    (b : (J₁ ⋙ Vsrc) ⋙ (I₂ ⋙ P) ≅ J₂ ⋙ S)
    (c : (K ⋙ Q₀) ⋙ (Hsrc ⋙ Stail) ≅ J₂ ⋙ Sright)
    (d : (I₁ ⋙ Q₁) ⋙ (I₂ ⋙ P) ≅ Hsrc ⋙ Stail)
    (e : J₂ ⋙ Sright ≅ J₂ ⋙ S) (ep : Sright ≅ S)
    (α : K ⋙ Q₀ ⋙ I₁ ⋙ Q₁ ⟶ J₁ ⋙ Vsrc)
    (β : J₁ ⋙ Vsrc ⋙ I₂ ⋙ P ⟶ J₂ ⋙ S)
    (γ : K ⋙ Q₀ ⋙ Hsrc ⋙ Stail ⟶ J₂ ⋙ Sright)
    (δ : I₁ ⋙ Q₁ ⋙ I₂ ⋙ P ⟶ Hsrc ⋙ Stail)
    (ha : OriginalIsoHomFormula a α) (hb : OriginalIsoHomFormula b β)
    (hc : OriginalIsoHomFormula c γ)
    (hd : OriginalIsoHomFormula d δ)
    (he : OriginalIsoHomFormula e (Functor.whiskerLeft J₂ ep.hom))
    (h : ImageCartesianCompositionEquation ep α β δ γ) :
    OpenCompositionEquation a (b ≪≫ e.symm) c d :=
  imageCompositionIso_of_homEquation a b c d e α β γ δ
    (Functor.whiskerLeft J₂ ep.hom)
    (NatTrans.ext (funext ha)) (NatTrans.ext (funext hb))
    (NatTrans.ext (funext hc)) (NatTrans.ext (funext hd))
    (NatTrans.ext (funext he)) h
end Cartesian
end CategoryTheory
