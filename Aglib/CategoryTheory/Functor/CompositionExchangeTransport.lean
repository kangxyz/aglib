/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.CompositionChoice
public import Aglib.CategoryTheory.NatTrans.ExchangePastingTransport

/-! # Descend original composition exchange through canonical model comparisons -/

@[expose] public section
namespace CategoryTheory

variable {A B C A' B' C' : Type*}
  [Category* A] [Category* B] [Category* C]
  [Category* A'] [Category* B'] [Category* C']
  {F M : A ⥤ B} {G N : B ⥤ C} {H O : A ⥤ C}
  {F' M' : A' ⥤ B'} {G' N' : B' ⥤ C'} {H' O' : A' ⥤ C'}
  {U : A ⥤ A'} {V : B ⥤ B'} {W : C ⥤ C'}

/-- Whole composition-exchange equation in the original contraction orientation. -/
def CompositionExchangeEquation
    (κ : F ⋙ G ≅ H) (κ' : F' ⋙ G' ≅ H')
    (βF : F ⋙ V ⟶ U ⋙ F') (βG : G ⋙ W ⟶ V ⋙ G')
    (βH : H ⋙ W ⟶ U ⋙ H') : Prop :=
  ∀ X, W.map (κ.hom.app X) ≫ βH.app X =
    βG.app (F.obj X) ≫ G'.map (βF.app X) ≫ κ'.hom.app (U.obj X)

/-- Five proved canonical comparison squares descend the original model law.
The theorem does not construct replacements for any of the specified maps. -/
theorem compositionExchangeEquation_transport
    (x : F ≅ M) (y : G ≅ N) (z : H ≅ O)
    (x' : F' ≅ M') (y' : G' ≅ N') (z' : H' ≅ O')
    (κ : F ⋙ G ≅ H) (κ' : F' ⋙ G' ≅ H')
    (μ : M ⋙ N ≅ O) (μ' : M' ⋙ N' ≅ O')
    (βF : F ⋙ V ⟶ U ⋙ F') (βG : G ⋙ W ⟶ V ⋙ G') (βH : H ⋙ W ⟶ U ⋙ H')
    (βM : M ⋙ V ⟶ U ⋙ M') (βN : N ⋙ W ⟶ V ⋙ N') (βO : O ⋙ W ⟶ U ⋙ O')
    (hκ : compositionPairIso x y ≪≫ μ = κ ≪≫ z)
    (hκ' : compositionPairIso x' y' ≪≫ μ' = κ' ≪≫ z')
    (hF : ExchangeModelComparisonEquation x x' βF βM)
    (hG : ExchangeModelComparisonEquation y y' βG βN)
    (hH : ExchangeModelComparisonEquation z z' βH βO)
    (hm : CompositionExchangeEquation μ μ' βM βN βO) :
    CompositionExchangeEquation κ κ' βF βG βH := by
  intro X
  have hκX := congrArg (fun e => e.hom.app X) hκ
  have hκX' := congrArg (fun e => e.hom.app (U.obj X)) hκ'
  simp only [compositionPairIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] at hκX hκX'
  have hFX := congrArg (fun t => t.app X) hF
  have hGX := congrArg (fun t => t.app (M.obj X)) hG
  have hHX := congrArg (fun t => t.app X) hH
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hFX hGX hHX
  have hnβ := βG.naturality (x.hom.app X)
  have hny₁ := y'.hom.naturality (V.map (x.hom.app X))
  have hny₂ := y'.hom.naturality (βF.app X)
  have hny₃ := y'.hom.naturality (x'.hom.app (U.obj X))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnβ hny₁ hny₂ hny₃
  apply (cancel_mono (z'.hom.app (U.obj X))).mp
  simp only [Category.assoc]
  rw [← hHX, ← W.map_comp_assoc, ← hκX]
  simp only [W.map_comp, Category.assoc]
  rw [hm X, ← Category.assoc (W.map (y.hom.app (M.obj X))), hGX]
  simp only [Category.assoc]
  rw [reassoc_of% hnβ, reassoc_of% hny₁]
  simp only [← N'.map_comp_assoc]
  rw [hFX]
  simp only [N'.map_comp, Category.assoc]
  rw [← reassoc_of% hny₂, ← reassoc_of% hny₃]
  simp only [Category.assoc] at hκX'
  rw [hκX']

end CategoryTheory
