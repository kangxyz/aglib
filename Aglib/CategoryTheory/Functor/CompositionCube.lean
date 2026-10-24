/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.CompositionSquare

/-!
# Source cubes for specified natural-isomorphism comparisons

Composition coherence for the two paths through a square, together with the
original middle transport, implies the source cube. All six comparison natural
isomorphisms are parameters before their components are evaluated. The current
consumer compares native module and abelian inverse images under scalar forgetting.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {A B C D A' B' C' D' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* A'] [Category* B'] [Category* C'] [Category* D']
  {L : A ⥤ B} {L' : C ⥤ D} {G : A ⥤ C} {H : B ⥤ D}
  {K : A' ⥤ B'} {K' : C' ⥤ D'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
  {L₀ L₁ : A ⥤ D} {K₀ K₁ : A' ⥤ D'}

/-- Composition coherence for the six specified natural comparisons yields the
original source cube, with its supplied whole-isomorphism normalizations. -/
theorem comparisonCube_app_of_composition
    (sL : L ⋙ QB ≅ QA ⋙ K) (sL' : L' ⋙ QD ≅ QC ⋙ K')
    (sG : G ⋙ QC ≅ QA ⋙ G') (sH : H ⋙ QD ≅ QB ⋙ H')
    (s₀ : L₀ ⋙ QD ≅ QA ⋙ K₀) (s₁ : L₁ ⋙ QD ≅ QA ⋙ K₁)
    (c₀ : L₀ ≅ G ⋙ L') (c₁ : L₁ ≅ L ⋙ H) (c : L₀ ≅ L₁)
    (d₀ : K₀ ≅ G' ⋙ K') (d₁ : K₁ ≅ K ⋙ H') (d : K₀ ≅ K₁)
    (sm : G ⋙ L' ≅ L ⋙ H) (sa : G' ⋙ K' ≅ K ⋙ H')
    (hsm : sm = c₀.symm ≪≫ c ≪≫ c₁) (hsa : sa = d₀.symm ≪≫ d ≪≫ d₁)
    (h₀ : ∀ X, d₀.hom.app (QA.obj X) ≫ K'.map (sG.inv.app X) ≫
      sL'.inv.app (G.obj X) = s₀.inv.app X ≫ QD.map (c₀.hom.app X))
    (h₁ : ∀ X, d₁.hom.app (QA.obj X) ≫ H'.map (sL.inv.app X) ≫
      sH.inv.app (L.obj X) = s₁.inv.app X ≫ QD.map (c₁.hom.app X))
    (h : ∀ X, d.hom.app (QA.obj X) ≫ s₁.inv.app X =
      s₀.inv.app X ≫ QD.map (c.hom.app X)) (X : A) :
    sa.hom.app (QA.obj X) ≫ H'.map (sL.inv.app X) ≫ sH.inv.app (L.obj X) =
      K'.map (sG.inv.app X) ≫ sL'.inv.app (G.obj X) ≫ QD.map (sm.hom.app X) :=
  comparisonSquare_app_of_composition QA QD c₀ c₁ c d₀ d₁ d sm sa hsm hsa X
    (K'.map (sG.inv.app X)) (sL'.inv.app (G.obj X))
    (H'.map (sL.inv.app X)) (sH.inv.app (L.obj X))
    (s₀.inv.app X) (s₁.inv.app X) (h₀ X) (h₁ X) (h X)

end CategoryTheory.Functor
