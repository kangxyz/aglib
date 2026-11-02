/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.NatTrans.SourceIsoToTarget
public import Aglib.CategoryTheory.NatTrans.CartesianSourceToTarget

/-! # Original horizontal pasting followed by the actual identity normalization -/
@[expose] public section
namespace CategoryTheory
open CategoryTheory.Functor
variable {A A' A'' B B' : Type*}
  [Category* A] [Category* A'] [Category* A''] [Category* B] [Category* B']
  {F : A ⥤ B} {F₁ : A' ⥤ B'} {F₂ : A'' ⥤ B'}
  {G G₀ : B ⥤ B'} {I : B' ⥤ B'}
  {H : A ⥤ A'} {E : A' ⥤ A''} {W W₀ : A ⥤ A''}

/-- The original horizontal equation retains all actual structural comparisons. -/
def IdentityBasePastingEquation
    (β₁ : F ⋙ G ⟶ H ⋙ F₁) (β₂ : F₁ ⋙ I ⟶ E ⋙ F₂)
    (β₀ : F ⋙ G₀ ⟶ W₀ ⋙ F₂) (cb : G₀ ≅ G ⋙ I) (cs : W₀ ≅ H ⋙ E) : Prop :=
  ∀ K, cb.hom.app (F.obj K) ≫ I.map (β₁.app K) ≫ β₂.app (H.obj K) =
    β₀.app K ≫ F₂.map (cs.hom.app K)

/-- Normalize the actual pasted mate; equality transport remains explicitly supplied. -/
theorem identityBasePasting_factor
    (β₁ : F ⋙ G ⟶ H ⋙ F₁) (β₂ : F₁ ⋙ I ⟶ E ⋙ F₂)
    (β₀ : F ⋙ G₀ ⟶ W₀ ⋙ F₂) (β : F ⋙ G ⟶ W ⋙ F₂)
    (cb : G₀ ≅ G ⋙ I) (cs : W₀ ≅ H ⋙ E) (c : W ≅ H ⋙ E)
    (eb : G₀ ≅ G) (es : W₀ ≅ W) (d : I ≅ 𝟭 B')
    (hb : cb ≪≫ isoWhiskerLeft G d ≪≫ rightUnitor G = eb)
    (hs : cs = es ≪≫ c)
    (ht : whiskerLeft F eb.hom ≫ β = β₀ ≫ whiskerRight es.hom F₂)
    (hp : IdentityBasePastingEquation β₁ β₂ β₀ cb cs) :
    CartesianSourceTargetFactorEquation β₁ (identityBaseExchange d β₂) c β := by
  intro K
  apply (cancel_epi (eb.hom.app (F.obj K))).1
  have hbK := congrArg (fun z => z.hom.app (F.obj K)) hb
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerLeft_app, rightUnitor_hom_app] at hbK
  have htK := congrArg (fun z => z.app K) ht
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at htK
  have hbK' : cb.hom.app (F.obj K) ≫ d.hom.app (G.obj (F.obj K)) =
      eb.hom.app (F.obj K) :=
    (congrArg (fun t => cb.hom.app (F.obj K) ≫ t)
      (Category.comp_id (d.hom.app (G.obj (F.obj K))))).symm.trans hbK
  rw [htK, ← hbK']
  simp only [identityBaseExchange, NatTrans.comp_app, rightUnitor_inv_app,
    whiskerLeft_app, Category.id_comp, Category.assoc]
  have hn : d.hom.app (G.obj (F.obj K)) ≫ β₁.app K =
      I.map (β₁.app K) ≫ d.hom.app (F₁.obj (H.obj K)) :=
    (d.hom.naturality (β₁.app K)).symm
  rw [reassoc_of% hn]
  simp only [Iso.hom_inv_id_app_assoc]
  have hpK := hp K
  rw [reassoc_of% hpK]
  simp only [hs, Iso.trans_hom, NatTrans.comp_app, F₂.map_comp, Category.assoc]
  rw [← F₂.map_comp, Iso.hom_inv_id_app, F₂.map_id, Category.comp_id]
end CategoryTheory
