/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HorizontalCube

/-! # Faithful descent of original coefficient adjunction mates

Both comparison cubes are required as equations. Invertibility of their
vertices alone never substitutes for compatibility of the original maps.
-/

@[expose] public section

namespace CategoryTheory

open TwoSquare

variable {A B C D A' B' C' D' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* A'] [Category* B'] [Category* C'] [Category* D']
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : C' ⥤ D'} {R₂' : D' ⥤ C'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}

/-- A faithful coefficient realization descends the actual mate equation. -/
theorem mateEquiv_eq_of_coefficient_cubes
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (a' : L₁' ⊣ R₁') (b' : L₂' ⊣ R₂')
    (s₁ : TwoSquare QA L₁ L₁' QB) (s₂ : TwoSquare QC L₂ L₂' QD)
    (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁' L₂' H')
    (γ : QA ⋙ G' ≅ G ⋙ QC) (δ : QB ⋙ H' ⟶ H ⋙ QD)
    (d₁ : R₁ ⋙ QA ⟶ QB ⋙ R₁') (d₂ : R₂ ⋙ QC ≅ QD ⋙ R₂')
    (μ : R₁ ⋙ G ⟶ H ⋙ R₂) (μ' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (hs₁ : (mateEquiv a a' s₁).natTrans = d₁)
    (hs₂ : (mateEquiv b b' s₂).natTrans = d₂.hom)
    (hα' : (mateEquiv a' b' α').natTrans = μ')
    (hleft : ∀ X, L₂'.map (γ.hom.app X) ≫ (α ≫ₕ s₂).app X =
      (s₁ ≫ₕ α').app X ≫ δ.app (L₁.obj X))
    (hright : ∀ K, G'.map (d₁.app K) ≫ μ'.app (QB.obj K) ≫ R₂'.map (δ.app K) =
      γ.hom.app (R₁.obj K) ≫ QC.map (μ.app K) ≫ d₂.hom.app (H.obj K))
    [QC.Faithful] : (mateEquiv a b α).natTrans = μ := by
  apply NatTrans.ext
  funext K
  apply QC.map_injective
  apply (cancel_epi (γ.hom.app (R₁.obj K))).mp
  apply (cancel_mono (d₂.hom.app (H.obj K))).mp
  have ht := mateEquiv_horizontal_cube a b a' b' s₁ s₂ α α'
    γ.hom δ hleft K
  change G'.map ((mateEquiv a a' s₁).natTrans.app K) ≫
      (mateEquiv a' b' α').natTrans.app (QB.obj K) ≫ R₂'.map (δ.app K) =
    γ.hom.app (R₁.obj K) ≫ QC.map ((mateEquiv a b α).natTrans.app K) ≫
      (mateEquiv b b' s₂).natTrans.app (H.obj K) at ht
  rw [hs₁, hs₂, hα'] at ht
  simpa only [Category.assoc] using ht.symm.trans (hright K)

end CategoryTheory
