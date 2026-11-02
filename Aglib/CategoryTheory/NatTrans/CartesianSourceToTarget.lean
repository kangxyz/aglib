/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.NatTrans.ExchangeToTarget

/-! # Source transport of the same canonical exchange square -/
@[expose] public section
namespace CategoryTheory
open CategoryTheory.Functor
variable {A A' A'' B B' : Type*}
  [Category* A] [Category* A'] [Category* A''] [Category* B] [Category* B']
  {F R : A ⥤ B} {G S : A' ⥤ B'} {H T : A'' ⥤ B'} {U : B ⥤ B'}
  {V : A ⥤ A'} {E : A' ⥤ A''} {W : A ⥤ A''}

/-- The literal ordinary-image factorization for a specified Cartesian presentation. -/
def CartesianSourceTargetFactorEquation (γ : R ⋙ U ⟶ V ⋙ S)
    (ψ : S ⟶ E ⋙ T) (c : W ≅ V ⋙ E) (δ : R ⋙ U ⟶ W ⋙ T) : Prop :=
  ∀ K, γ.app K ≫ ψ.app (V.obj K) ≫ T.map (c.inv.app K) = δ.app K

/-- Paste actual exchange and source-comparison squares, retaining the given original map. -/
theorem cartesianSource_toTarget (b : F ⟶ R) (b' : G ⟶ S) (b'' : H ⟶ T)
    (β : F ⋙ U ⟶ V ⋙ G) (γ : R ⋙ U ⟶ V ⋙ S)
    (s : G ⟶ E ⋙ H) (ψ : S ⟶ E ⋙ T) (c : W ≅ V ⋙ E)
    (β' : F ⋙ U ⟶ W ⋙ H) (δ : R ⋙ U ⟶ W ⋙ T)
    (hβ' : ∀ K, β'.app K = β.app K ≫ s.app (V.obj K) ≫ H.map (c.inv.app K))
    (hβ : ExchangeToTargetEquation b b' β γ)
    (hs : TargetComparisonEquation s (whiskerLeft E b'') (b' ≫ ψ))
    (hδ : CartesianSourceTargetFactorEquation γ ψ c δ) :
    ExchangeToTargetEquation b b'' β' δ := by
  ext K
  have hb := congrArg (fun z => z.app K) hβ
  have hsource := congrArg (fun z => z.app (V.obj K)) hs
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hb hsource ⊢
  rw [hβ', Category.assoc, Category.assoc, b''.naturality]
  rw [reassoc_of% hsource]
  rw [← Category.assoc (β.app K), hb]
  simp only [Category.assoc]
  rw [hδ]
end CategoryTheory
