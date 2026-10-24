/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.ImageMates
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImageSquares
public import Aglib.CategoryTheory.Adjunction.Mates.ScalarForgettingCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeHorizontalUnit

/-! # Original module exchange and scalar-forgetting comparison

The exchange for every commuting square is the mate of the original module
inverse-image square under its native adjunctions. Scalar forgetting identifies
this literal map with the original abelian exchange through the actual underlying
comparisons. No cartesianness, finite morphism or coefficient restriction is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

private def ScalarSquareEquation
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    (U : A ⥤ A') (V : B ⥤ B') {P Q : A ⥤ B} {P' Q' : A' ⥤ B'}
    (α : P ⟶ Q) (α' : P' ⟶ Q')
    (s : ∀ X, P'.obj (U.obj X) ⟶ V.obj (P.obj X))
    (t : ∀ X, Q'.obj (U.obj X) ⟶ V.obj (Q.obj X)) (X : A) : Prop :=
  s X ≫ V.map (α.app X) = α'.app (U.obj X) ≫ t X

private theorem conjugateFamily_eqToHom
    {C D : Type*} [Category* C] [Category* D] {I : Sort*}
    (L : I → C ⥤ D) (R : I → D ⥤ C) (a : ∀ i, L i ⊣ R i)
    {i j : I} (h : i = j) :
    conjugateEquiv (a j) (a i) (eqToHom (congrArg L h)) =
      eqToHom (congrArg R h.symm) := by
  subst j
  exact conjugateEquiv_id (a i)

private theorem conjugate_inv_of_hom
    {C D : Type*} [Category* C] [Category* D]
    {L₀ L₁ : C ⥤ D} {R₀ R₁ : D ⥤ C}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (e : L₁ ≅ L₀) (r : R₀ ≅ R₁)
    (he : conjugateEquiv a₀ a₁ e.hom = r.hom) :
    conjugateEquiv a₁ a₀ e.inv = r.inv := by
  apply (cancel_epi r.hom).mp
  rw [← he, conjugateEquiv_comp, Iso.inv_hom_id, conjugateEquiv_id, he,
    Iso.hom_inv_id]

private theorem conjugate_iso_chain_of_eq
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

private theorem scalarSquare_of_conjugateSquare
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

private theorem scalarComparison_mate_of_squareEquation
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

end ProtectedCube

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

variable {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The original module inverse-image square uses the native composition comparisons. -/
def moduleInverseImageSquareIso :
    moduleInverseImage R g ⋙ moduleInverseImage R f' ≅
      moduleInverseImage R f ⋙ moduleInverseImage R g' :=
  (moduleInverseImageComp R g f').symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => moduleInverseImage R k) h) ≪≫
      moduleInverseImageComp R f g'

/-- The original module exchange is the native mate of its inverse-image square. -/
def moduleBaseChangeMap :
    moduleDirectImage R f ⋙ moduleInverseImage R g ⟶
      moduleInverseImage R g' ⋙ moduleDirectImage R f' :=
  (mateEquiv (moduleImageAdjunction R f) (moduleImageAdjunction R f')
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso R f f' g g' h).hom)).natTrans

/-- The literal original unit, square and counit formula for module exchange. -/
@[reassoc]
theorem moduleBaseChangeMap_app (F : ModuleSheaf R X) :
    (moduleBaseChangeMap R f f' g g' h).app F =
      (moduleImageAdjunction R f').unit.app
          ((moduleInverseImage R g).obj ((moduleDirectImage R f).obj F)) ≫
        (moduleDirectImage R f').map
          ((moduleInverseImageSquareIso R f f' g g' h).hom.app
            ((moduleDirectImage R f).obj F)) ≫
        (moduleDirectImage R f').map
          ((moduleInverseImage R g').map ((moduleImageAdjunction R f).counit.app F)) :=
  mateEquiv_app_eq (moduleImageAdjunction R f) (moduleImageAdjunction R f')
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso R f f' g g' h).hom) F

/-- The original module counit characterizes the adjoint of the native exchange. -/
@[reassoc]
theorem moduleBaseChangeMap_counit (F : ModuleSheaf R X) :
    (moduleInverseImage R f').map ((moduleBaseChangeMap R f f' g g' h).app F) ≫
        (moduleImageAdjunction R f').counit.app ((moduleInverseImage R g').obj F) =
      (moduleInverseImageSquareIso R f f' g g' h).hom.app ((moduleDirectImage R f).obj F) ≫
        (moduleInverseImage R g').map ((moduleImageAdjunction R f).counit.app F) :=
  mateEquiv_counit (moduleImageAdjunction R f) (moduleImageAdjunction R f')
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso R f f' g g' h).hom) F

/-- The native original module direct-image square. -/
def moduleDirectImageSquareIso :
    moduleDirectImage R g' ⋙ moduleDirectImage R f ≅
      moduleDirectImage R f' ⋙ moduleDirectImage R g :=
  moduleDirectImageCompIso R f g' ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => moduleDirectImage R k) h.symm) ≪≫
      (moduleDirectImageCompIso R g f').symm

/-- The actual module inverse-image square has the original direct-image square as conjugate. -/
theorem conjugateEquiv_moduleInverseImageSquareIso_hom :
    conjugateEquiv ((moduleImageAdjunction R f).comp (moduleImageAdjunction R g'))
      ((moduleImageAdjunction R g).comp (moduleImageAdjunction R f'))
      (moduleInverseImageSquareIso R f f' g g' h).hom =
        (moduleDirectImageSquareIso R f f' g g' h).hom :=
  conjugate_iso_chain_of_eq
    ((moduleImageAdjunction R f).comp (moduleImageAdjunction R g'))
    (moduleImageAdjunction R (g' ≫ f)) (moduleImageAdjunction R (f' ≫ g))
    ((moduleImageAdjunction R g).comp (moduleImageAdjunction R f'))
    (moduleInverseImageComp R f g')
    (eqToIso (congrArg (fun k : X' ⟶ S => moduleInverseImage R k) h))
    (moduleInverseImageComp R g f') (moduleDirectImageCompIso R f g')
    (eqToIso (congrArg (fun k : X' ⟶ S => moduleDirectImage R k) h.symm))
    (moduleDirectImageCompIso R g f').symm
    (moduleInverseImageSquareIso R f f' g g' h)
    (moduleDirectImageSquareIso R f f' g g' h) rfl rfl
    (conjugateEquiv_moduleInverseImageComp_hom R f g')
    (conjugateFamily_eqToHom (fun k : X' ⟶ S => moduleInverseImage R k)
      (fun k : X' ⟶ S => moduleDirectImage R k) (fun k => moduleImageAdjunction R k) h)
    (conjugate_inv_of_hom
      ((moduleImageAdjunction R g).comp (moduleImageAdjunction R f'))
      (moduleImageAdjunction R (f' ≫ g))
      (moduleInverseImageComp R g f') (moduleDirectImageCompIso R g f')
      (conjugateEquiv_moduleInverseImageComp_hom R g f'))

/-- Scalar compatibility of the original inverse square follows from its whole right mate. -/
private theorem moduleInverseImageSquareIso_underlying (F : ModuleSheaf R S) :
    ScalarSquareEquation (moduleUnderlying R S) (moduleUnderlying R X')
      (moduleInverseImageSquareIso R f f' g g' h).hom
      (inverseImageSquareIso f f' g g' h).hom
      (fun M => (inverseImage f').map ((moduleInverseImageUnderlyingIso R g).inv.app M) ≫
        (moduleInverseImageUnderlyingIso R f').inv.app ((moduleInverseImage R g).obj M))
      (fun M => (inverseImage g').map ((moduleInverseImageUnderlyingIso R f).inv.app M) ≫
        (moduleInverseImageUnderlyingIso R g').inv.app ((moduleInverseImage R f).obj M)) F :=
  scalarSquare_of_conjugateSquare
    (moduleImageAdjunction R f) (moduleImageAdjunction R f')
    (inverseImageAdjunction f) (inverseImageAdjunction f')
    (moduleImageAdjunction R g) (moduleImageAdjunction R g')
    (inverseImageAdjunction g) (inverseImageAdjunction g')
    (moduleInverseImageUnderlyingIso R f) (moduleInverseImageUnderlyingIso R f')
    (moduleInverseImageUnderlyingIso R g) (moduleInverseImageUnderlyingIso R g')
    (moduleDirectImageUnderlyingIso R f) (moduleDirectImageUnderlyingIso R f')
    (moduleDirectImageUnderlyingIso R g) (moduleDirectImageUnderlyingIso R g')
    (moduleInverseImageSquareIso R f f' g g' h).hom
    (inverseImageSquareIso f f' g g' h).hom
    (moduleDirectImageSquareIso R f f' g g' h).hom
    (directImageSquareIso f f' g g' h).hom
    (conjugateEquiv_moduleInverseImageSquareIso_hom R f f' g g' h)
    (conjugateEquiv_inverseImageSquareIso_hom f f' g g' h)
    (moduleUnderlyingImageSquare_mate R f) (moduleUnderlyingImageSquare_mate R f')
    (moduleUnderlyingImageSquare_mate R g) (moduleUnderlyingImageSquare_mate R g')
    (ModuleCat.Sheaf.pushforwardUnderlyingIso_square R
      (siteBaseChange f) (siteBaseChange g') (siteBaseChange g) (siteBaseChange f')
      S.smallEtaleTopology X.smallEtaleTopology S'.smallEtaleTopology X'.smallEtaleTopology
      (fun k : X' ⟶ S => siteBaseChange k) h.symm
      (siteBaseChangeComp f g').symm (siteBaseChangeComp g f').symm
      (moduleDirectImageSquareIso R f f' g g' h)
      (directImageSquareIso f f' g g' h) rfl rfl) F

/-- The actual underlying comparison at the source of module exchange. -/
def moduleBaseChangeSourceUnderlyingIso :
    (moduleDirectImage R f ⋙ moduleInverseImage R g) ⋙ moduleUnderlying R S' ≅
      moduleUnderlying R X ⋙ (directImage f ⋙ inverseImage g) :=
  scalarMateSourceIso (moduleDirectImageUnderlyingIso R f)
    (moduleInverseImageUnderlyingIso R g)

/-- The actual underlying comparison at the target of module exchange. -/
def moduleBaseChangeTargetUnderlyingIso :
    (moduleInverseImage R g' ⋙ moduleDirectImage R f') ⋙ moduleUnderlying R S' ≅
      moduleUnderlying R X ⋙ (inverseImage g' ⋙ directImage f') :=
  scalarMateTargetIso (moduleDirectImageUnderlyingIso R f')
    (moduleInverseImageUnderlyingIso R g')

/-- The literal module mate forgets to the literal original abelian mate,
through the actual source and target underlying-sheaf isomorphisms. -/
@[reassoc]
theorem moduleBaseChangeMap_underlying_app (F : ModuleSheaf R X) :
    (moduleUnderlying R S').map ((moduleBaseChangeMap R f f' g g' h).app F) ≫
        (moduleBaseChangeTargetUnderlyingIso R f' g').hom.app F =
      (moduleBaseChangeSourceUnderlyingIso R f g).hom.app F ≫
        (baseChangeMap f f' g g' h).app ((moduleUnderlying R X).obj F) :=
  scalarComparison_mate_of_squareEquation
    (moduleImageAdjunction R f) (moduleImageAdjunction R f')
    (inverseImageAdjunction f) (inverseImageAdjunction f')
    (moduleInverseImageUnderlyingIso R f) (moduleInverseImageUnderlyingIso R f')
    (moduleDirectImageUnderlyingIso R f) (moduleDirectImageUnderlyingIso R f')
    (moduleInverseImageUnderlyingIso R g) (moduleInverseImageUnderlyingIso R g')
    (moduleInverseImageSquareIso R f f' g g' h).hom
    (inverseImageSquareIso f f' g g' h).hom
    (moduleBaseChangeMap R f f' g g' h) (baseChangeMap f f' g g' h) rfl rfl
    (moduleBaseChangeSourceUnderlyingIso R f g)
    (moduleBaseChangeTargetUnderlyingIso R f' g') rfl rfl
    (moduleUnderlyingImageSquare_mate R f) (moduleUnderlyingImageSquare_mate R f')
    (moduleInverseImageSquareIso_underlying R f f' g g' h) F

/-- The entire original natural transformation, not merely its isomorphism class,
commutes with scalar forgetting and the native underlying comparisons. -/
theorem moduleBaseChangeMap_underlying :
    Functor.whiskerRight (moduleBaseChangeMap R f f' g g' h) (moduleUnderlying R S') ≫
        (moduleBaseChangeTargetUnderlyingIso R f' g').hom =
      (moduleBaseChangeSourceUnderlyingIso R f g).hom ≫
        Functor.whiskerLeft (moduleUnderlying R X) (baseChangeMap f f' g g' h) := by
  apply NatTrans.ext
  funext F
  exact moduleBaseChangeMap_underlying_app R f f' g g' h F

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
