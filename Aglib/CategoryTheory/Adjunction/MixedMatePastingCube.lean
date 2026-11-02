/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.MixedMateBaseChange

/-! # The left mixed-mate cube from two original pasting equations -/

@[expose] public section

namespace CategoryTheory

variable {A B C D A' B' C' D' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* A'] [Category* B'] [Category* C'] [Category* D']
  {L₁ : A ⥤ B} {L₂ : C ⥤ D} {L₁' : A' ⥤ B'} {L₂' : C' ⥤ D'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
  {TA TB : A ⥤ B'} {TC TD : C ⥤ D'}

/-- A whole original first-route pasting equation. -/
def MixedMateFirstRoute
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (eH : H ⋙ QD ≅ QB ⋙ H')
    (p : G ⋙ TC ≅ TA ⋙ H') (a : TA ≅ L₁ ⋙ QB) (c : TC ≅ L₂ ⋙ QD) : Prop :=
  ∀ X, c.hom.app (G.obj X) ≫ QD.map (α.app X) ≫ eH.hom.app (L₁.obj X) =
    p.hom.app X ≫ H'.map (a.hom.app X)

/-- A whole original second-route pasting equation. -/
def MixedMateSecondRoute
    (α' : G' ⋙ L₂' ⟶ L₁' ⋙ H') (eG : G ⋙ QC ≅ QA ⋙ G')
    (p : G ⋙ TD ≅ TB ⋙ H') (a : TB ≅ QA ⋙ L₁') (c : TD ≅ QC ⋙ L₂') : Prop :=
  ∀ X, c.hom.app (G.obj X) ≫ L₂'.map (eG.hom.app X) ≫ α'.app (QA.obj X) =
    p.hom.app X ≫ H'.map (a.hom.app X)

/-- Whole transport between the two total original open comparisons. -/
def MixedMateTotalTransport
    (p : G ⋙ TC ≅ TA ⋙ H') (q : G ⋙ TD ≅ TB ⋙ H')
    (a : TB ≅ TA) (c : TD ≅ TC) : Prop :=
  ∀ X, c.hom.app (G.obj X) ≫ p.hom.app X = q.hom.app X ≫ H'.map (a.hom.app X)

/-- Two proved pasting routes and their actual total transport imply the left
cube. No replacement comparison or desired cube is supplied as a hypothesis. -/
theorem mixedMateLeftCube_of_pasting
    (s₁ : QA ⋙ L₁' ≅ L₁ ⋙ QB) (s₂ : QC ⋙ L₂' ≅ L₂ ⋙ QD)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (α' : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    (eG : G ⋙ QC ≅ QA ⋙ G') (eH : H ⋙ QD ≅ QB ⋙ H')
    (p : G ⋙ TC ≅ TA ⋙ H') (q : G ⋙ TD ≅ TB ⋙ H')
    (a : TA ≅ L₁ ⋙ QB) (b : TB ≅ QA ⋙ L₁')
    (c : TC ≅ L₂ ⋙ QD) (d : TD ≅ QC ⋙ L₂')
    (t : TB ≅ TA) (v : TD ≅ TC)
    (hs₁ : s₁ = b.symm ≪≫ t ≪≫ a) (hs₂ : s₂ = d.symm ≪≫ v ≪≫ c)
    (hp : MixedMateFirstRoute α eH p a c)
    (hq : MixedMateSecondRoute α' eG q b d)
    (ht : MixedMateTotalTransport p q t v) :
    MixedMateLeftCube s₁.hom s₂.hom α α' eG eH := by
  intro X
  have hq' := congrArg
    (fun z => d.inv.app (G.obj X) ≫ z ≫ H'.map (b.inv.app X)) (hq X)
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← H'.map_comp,
    Iso.hom_inv_id_app, Functor.map_id] at hq'
  simp only [Functor.comp_obj, Category.comp_id] at hq'
  have hf : s₂.hom.app (G.obj X) ≫ QD.map (α.app X) ≫
      eH.hom.app (L₁.obj X) =
    L₂'.map (eG.hom.app X) ≫ α'.app (QA.obj X) ≫ H'.map (s₁.hom.app X) := by
    rw [hs₁, hs₂]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
      Category.assoc]
    rw [hp X, reassoc_of% (ht X)]
    rw [← reassoc_of% hq']
  have hi := congrArg
    (fun z => L₂'.map (eG.inv.app X) ≫ z ≫ eH.inv.app (L₁.obj X)) hf
  simp only [Category.assoc, Iso.hom_inv_id_app,
    ← L₂'.map_comp_assoc, Iso.inv_hom_id_app, L₂'.map_id, Category.id_comp] at hi
  simpa only [Functor.comp_obj, Category.comp_id] using hi

end CategoryTheory
