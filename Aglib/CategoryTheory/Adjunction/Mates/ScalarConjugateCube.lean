/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.ScalarForgettingCoherence

/-! # Original scalar comparisons from the conjugate cube

Equality transports and original conjugate chains identify the left scalar
square from the actual right square. The existing mate comparison then gives
the whole original exchanged transformation, retaining all eight independent
category and Hom worlds and all supplied adjunctions and comparison maps.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.ScalarConjugateCube

/-- The original left scalar comparison square at a specified object. -/
def ScalarSquareEquation
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    (U : A ⥤ A') (V : B ⥤ B') {P Q : A ⥤ B} {P' Q' : A' ⥤ B'}
    (α : P ⟶ Q) (α' : P' ⟶ Q')
    (s : ∀ X, P'.obj (U.obj X) ⟶ V.obj (P.obj X))
    (t : ∀ X, Q'.obj (U.obj X) ⟶ V.obj (Q.obj X)) (X : A) : Prop :=
  s X ≫ V.map (α.app X) = α'.app (U.obj X) ≫ t X

/-- Conjugating original equality transport gives the inverse equality of right adjoints. -/
theorem conjugateFamily_eqToHom
    {C D : Type*} [Category* C] [Category* D] {I : Sort*}
    (L : I → C ⥤ D) (R : I → D ⥤ C) (a : ∀ i, L i ⊣ R i)
    {i j : I} (h : i = j) :
    conjugateEquiv (a j) (a i) (eqToHom (congrArg L h)) =
      eqToHom (congrArg R h.symm) := by
  subst j
  exact conjugateEquiv_id (a i)

/-- The inverse comparison has the inverse original conjugate. -/
theorem conjugate_inv_of_hom
    {C D : Type*} [Category* C] [Category* D]
    {L₀ L₁ : C ⥤ D} {R₀ R₁ : D ⥤ C}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (e : L₁ ≅ L₀) (r : R₀ ≅ R₁)
    (he : conjugateEquiv a₀ a₁ e.hom = r.hom) :
    conjugateEquiv a₁ a₀ e.inv = r.inv := by
  apply (cancel_epi r.hom).mp
  rw [← he, conjugateEquiv_comp, Iso.inv_hom_id, conjugateEquiv_id, he,
    Iso.hom_inv_id]

/-- The original three-factor left comparison has its specified right conjugate chain. -/
theorem conjugate_iso_chain_of_eq
    {C D : Type*} [Category* C] [Category* D]
    {L₀ L₁ L₂ L₃ : C ⥤ D} {R₀ R₁ R₂ R₃ : D ⥤ C}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (e₀ : L₁ ≅ L₀) (m : L₂ ≅ L₁) (e₁ : L₂ ≅ L₃)
    (r₀ : R₀ ≅ R₁) (rₘ : R₁ ≅ R₂) (r₁ : R₂ ≅ R₃)
    (p : L₃ ≅ L₀) (q : R₀ ≅ R₃)
    (hp : p = e₁.symm ≪≫ m ≪≫ e₀) (hq : q = r₀ ≪≫ rₘ ≪≫ r₁)
    (h₀ : conjugateEquiv a₀ a₁ e₀.hom = r₀.hom)
    (hₘ : conjugateEquiv a₁ a₂ m.hom = rₘ.hom)
    (h₁ : conjugateEquiv a₂ a₃ e₁.inv = r₁.hom) :
    conjugateEquiv a₀ a₃ p.hom = q.hom := by
  subst p
  subst q
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← conjugateEquiv_comp a₀ a₂ a₃, ← conjugateEquiv_comp a₀ a₁ a₂,
    h₀, hₘ, h₁, Category.assoc]

section ProtectedCube

variable {A B C D A' B' C' D' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* A'] [Category* B'] [Category* C'] [Category* D']
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : C' ⥤ D'} {R₂' : D' ⥤ C'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}

/-- An actual right conjugate square gives the original left scalar square. -/
theorem scalarSquare_of_conjugateSquare
    {RG : C ⥤ A} {RH : D ⥤ B} {RG' : C' ⥤ A'} {RH' : D' ⥤ B'}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (adjG : G ⊣ RG) (adjH : H ⊣ RH) (adjG' : G' ⊣ RG') (adjH' : H' ⊣ RH')
    (e₁ : L₁ ⋙ QB ≅ QA ⋙ L₁') (e₂ : L₂ ⋙ QD ≅ QC ⋙ L₂')
    (eG : G ⋙ QC ≅ QA ⋙ G') (eH : H ⋙ QD ≅ QB ⋙ H')
    (r₁ : R₁ ⋙ QA ≅ QB ⋙ R₁') (r₂ : R₂ ⋙ QC ≅ QD ⋙ R₂')
    (rG : RG ⋙ QA ≅ QC ⋙ RG') (rH : RH ⋙ QB ≅ QD ⋙ RH')
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (α' : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    (q : RH ⋙ R₁ ⟶ R₂ ⋙ RG) (q' : RH' ⋙ R₁' ⟶ R₂' ⋙ RG')
    (hq : conjugateEquiv (adj₁.comp adjH) (adjG.comp adj₂) α = q)
    (hq' : conjugateEquiv (adj₁'.comp adjH') (adjG'.comp adj₂') α' = q')
    (he₁ : mateEquiv adj₁ adj₁' (TwoSquare.mk _ _ _ _ e₁.inv) =
      TwoSquare.mk _ _ _ _ r₁.hom)
    (he₂ : mateEquiv adj₂ adj₂' (TwoSquare.mk _ _ _ _ e₂.inv) =
      TwoSquare.mk _ _ _ _ r₂.hom)
    (heG : mateEquiv adjG adjG' (TwoSquare.mk _ _ _ _ eG.inv) =
      TwoSquare.mk _ _ _ _ rG.hom)
    (heH : mateEquiv adjH adjH' (TwoSquare.mk _ _ _ _ eH.inv) =
      TwoSquare.mk _ _ _ _ rH.hom)
    (hr : ∀ M, QA.map (q.app M) ≫ rG.hom.app (R₂.obj M) ≫ RG'.map (r₂.hom.app M) =
      (r₁.hom.app (RH.obj M) ≫ R₁'.map (rH.hom.app M)) ≫ q'.app (QD.obj M)) (X : A) :
    ScalarSquareEquation QA QD α α'
      (fun Y => L₂'.map (eG.inv.app Y) ≫ e₂.inv.app (G.obj Y))
      (fun Y => H'.map (e₁.inv.app Y) ≫ eH.inv.app (L₁.obj Y)) X := by
  let Es := TwoSquare.vComp (TwoSquare.mk _ _ _ _ eG.inv) (TwoSquare.mk _ _ _ _ e₂.inv)
  let Et := TwoSquare.vComp (TwoSquare.mk _ _ _ _ e₁.inv) (TwoSquare.mk _ _ _ _ eH.inv)
  have hs : Es.whiskerLeft α = Et.whiskerRight α' := by
    apply (mateEquiv (adj₁.comp adjH) (adjG'.comp adj₂')).injective
    rw [conjugateEquiv_mateEquiv_vcomp, mateEquiv_conjugateEquiv_vcomp, hq, hq']
    ext M
    simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app]
    dsimp only [Es, Et]
    rw [mateEquiv_vComp_app, mateEquiv_vComp_app, heG, he₂, he₁, heH]
    exact hr M
  simpa only [ScalarSquareEquation, TwoSquare.whiskerLeft_app,
    TwoSquare.whiskerRight_app, Es, Et, TwoSquare.vComp_app] using
      congrArg (fun s => s.app X) hs

/-- The original left scalar square identifies the actual mate components. -/
theorem scalarComparison_mate_of_squareEquation
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (e₁ : L₁ ⋙ QB ≅ QA ⋙ L₁') (e₂ : L₂ ⋙ QD ≅ QC ⋙ L₂')
    (r₁ : R₁ ⋙ QA ≅ QB ⋙ R₁') (r₂ : R₂ ⋙ QC ≅ QD ⋙ R₂')
    (eG : G ⋙ QC ≅ QA ⋙ G') (eH : H ⋙ QD ≅ QB ⋙ H')
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (α' : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) (β' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (hβ : β = (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).natTrans)
    (hβ' : β' = (mateEquiv adj₁' adj₂' (TwoSquare.mk _ _ _ _ α')).natTrans)
    (s : (R₁ ⋙ G) ⋙ QC ≅ QB ⋙ (R₁' ⋙ G'))
    (t : (H ⋙ R₂) ⋙ QC ≅ QB ⋙ (H' ⋙ R₂'))
    (hs : s = scalarMateSourceIso r₁ eG) (ht : t = scalarMateTargetIso r₂ eH)
    (he₁ : mateEquiv adj₁ adj₁' (TwoSquare.mk _ _ _ _ e₁.inv) =
      TwoSquare.mk _ _ _ _ r₁.hom)
    (he₂ : mateEquiv adj₂ adj₂' (TwoSquare.mk _ _ _ _ e₂.inv) =
      TwoSquare.mk _ _ _ _ r₂.hom)
    (h : ∀ X, ScalarSquareEquation QA QD α α'
      (fun Y => L₂'.map (eG.inv.app Y) ≫ e₂.inv.app (G.obj Y))
      (fun Y => H'.map (e₁.inv.app Y) ≫ eH.inv.app (L₁.obj Y)) X) (K : B) :
    QC.map (β.app K) ≫ t.hom.app K = s.hom.app K ≫ β'.app (QB.obj K) :=
  scalarComparison_mate adj₁ adj₂ adj₁' adj₂' e₁ e₂ r₁ r₂ eG eH
    α α' β β' hβ hβ' s t hs ht he₁ he₂ (fun X => h X) K

/-- The actual right conjugate square identifies the whole original mate square
through its fixed scalar comparisons. No exchange isomorphism is assumed. -/
theorem scalarComparison_mate_whole_of_conjugateSquare
    {RG : C ⥤ A} {RH : D ⥤ B} {RG' : C' ⥤ A'} {RH' : D' ⥤ B'}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (adjG : G ⊣ RG) (adjH : H ⊣ RH) (adjG' : G' ⊣ RG') (adjH' : H' ⊣ RH')
    (e₁ : L₁ ⋙ QB ≅ QA ⋙ L₁') (e₂ : L₂ ⋙ QD ≅ QC ⋙ L₂')
    (eG : G ⋙ QC ≅ QA ⋙ G') (eH : H ⋙ QD ≅ QB ⋙ H')
    (r₁ : R₁ ⋙ QA ≅ QB ⋙ R₁') (r₂ : R₂ ⋙ QC ≅ QD ⋙ R₂')
    (rG : RG ⋙ QA ≅ QC ⋙ RG') (rH : RH ⋙ QB ≅ QD ⋙ RH')
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (α' : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    (q : RH ⋙ R₁ ⟶ R₂ ⋙ RG) (q' : RH' ⋙ R₁' ⟶ R₂' ⋙ RG')
    (hq : conjugateEquiv (adj₁.comp adjH) (adjG.comp adj₂) α = q)
    (hq' : conjugateEquiv (adj₁'.comp adjH') (adjG'.comp adj₂') α' = q')
    (he₁ : mateEquiv adj₁ adj₁' (TwoSquare.mk _ _ _ _ e₁.inv) =
      TwoSquare.mk _ _ _ _ r₁.hom)
    (he₂ : mateEquiv adj₂ adj₂' (TwoSquare.mk _ _ _ _ e₂.inv) =
      TwoSquare.mk _ _ _ _ r₂.hom)
    (heG : mateEquiv adjG adjG' (TwoSquare.mk _ _ _ _ eG.inv) =
      TwoSquare.mk _ _ _ _ rG.hom)
    (heH : mateEquiv adjH adjH' (TwoSquare.mk _ _ _ _ eH.inv) =
      TwoSquare.mk _ _ _ _ rH.hom)
    (hr : ∀ M, QA.map (q.app M) ≫ rG.hom.app (R₂.obj M) ≫ RG'.map (r₂.hom.app M) =
      (r₁.hom.app (RH.obj M) ≫ R₁'.map (rH.hom.app M)) ≫ q'.app (QD.obj M))
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) (β' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (hβ : β = (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).natTrans)
    (hβ' : β' = (mateEquiv adj₁' adj₂' (TwoSquare.mk _ _ _ _ α')).natTrans)
    (s : (R₁ ⋙ G) ⋙ QC ≅ QB ⋙ (R₁' ⋙ G'))
    (t : (H ⋙ R₂) ⋙ QC ≅ QB ⋙ (H' ⋙ R₂'))
    (hs : s = scalarMateSourceIso r₁ eG) (ht : t = scalarMateTargetIso r₂ eH) :
    Functor.whiskerRight β QC ≫ t.hom = s.hom ≫ Functor.whiskerLeft QB β' := by
  apply NatTrans.ext
  funext K
  exact scalarComparison_mate_of_squareEquation adj₁ adj₂ adj₁' adj₂'
    e₁ e₂ r₁ r₂ eG eH α α' β β' hβ hβ' s t hs ht he₁ he₂
    (fun X => scalarSquare_of_conjugateSquare adj₁ adj₂ adj₁' adj₂'
      adjG adjH adjG' adjH' e₁ e₂ eG eH r₁ r₂ rG rH α α' q q' hq hq'
      he₁ he₂ heG heH hr X) K

end ProtectedCube

end CategoryTheory.ScalarConjugateCube
