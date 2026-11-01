/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uB uA' vA vB vA'

variable {A : Type uA} {B : Type uB} {A' : Type uA'} [Category.{vA} A] [Category.{vB} B]
  [Category.{vA'} A']
  {F : A ⥤ B} {I : B ⥤ B} {V : A ⥤ A'} {R D N : A' ⥤ B}

/-- Original normalized identity base change with explicit source transport and
original identity-comparison transition. -/
def NormalizedIdentityBaseChangeEquation
    (β : F ⋙ I ⟶ V ⋙ N) (i : I ≅ 𝟭 B) (s : F ≅ V ⋙ D) (τ : D ⟶ N) : Prop :=
  β = Functor.whiskerLeft F i.hom ≫ (Functor.rightUnitor F).hom ≫
    s.hom ≫ Functor.whiskerLeft V τ

/-- Original raw naturality, original source transport, and the actual ambient
transition triangle imply normalized identity base change. -/
theorem normalizedIdentityBaseChangeEquation
    (δ : F ⟶ F) (βr : F ⋙ I ⟶ V ⋙ R) (βs : F ⋙ I ⟶ V ⋙ D)
    (t : D ⟶ R) (n : R ⟶ N) (τ : D ⟶ N) (βn : F ⋙ I ⟶ V ⋙ N)
    (i : I ≅ 𝟭 B) (s : F ≅ V ⋙ D)
    (hnat : ExchangeNaturalityEquation δ βr βs t) (hδ : δ = 𝟙 F)
    (hsource : SourceIsoExchangeEquation βs i s)
    (htriangle : t ≫ n = τ) (hn : βn = βr ≫ Functor.whiskerLeft V n) :
    NormalizedIdentityBaseChangeEquation βn i s τ := by
  have hs : βs = Functor.whiskerLeft F i.hom ≫ (Functor.rightUnitor F).hom ≫ s.hom := by
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
    exact (hsource K).trans
      (congrArg (fun z => i.hom.app (F.obj K) ≫ z)
        (Category.id_comp (s.hom.app K))).symm
  have hr : βr = βs ≫ Functor.whiskerLeft V t := by
    change Functor.whiskerRight δ I ≫ βr = _ at hnat
    simpa only [hδ, Functor.whiskerRight_id', Category.id_comp] using hnat
  change βn = _
  rw [hn, hr, Category.assoc, ← Functor.whiskerLeft_comp, htriangle, hs]
  simp only [Category.assoc]

end CategoryTheory
