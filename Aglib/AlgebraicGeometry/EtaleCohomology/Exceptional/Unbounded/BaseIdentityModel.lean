/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeIdentity
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ChangeTarget
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.SpecifiedMateCube
public import Aglib.Algebra.Homology.HomologicalComplex.Mates
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ModelComparisonCoherence

/-! # Identity base change between two actual base derived models

The source model is fixed and both base models are explicit. The base transport
is exactly `Localization.uniq`, with its original `compUniqFunctor`. All maps
are normalized on full cochain complexes, never by bounded-below restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

private theorem factor_mate_of_counit
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    {Q : A ⥤ A'} {P : B ⥤ B'} (a : L ⊣ R) (b : L' ⊣ R')
    (l : Q ⋙ L' ⟶ L ⋙ P) (r : R ⋙ Q ⟶ P ⋙ R')
    (h : ∀ K, L'.map (r.app K) ≫ b.counit.app (P.obj K) =
      l.app (R.obj K) ≫ P.map (a.counit.app K)) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _ l)).natTrans = r :=
  ((eq_mateEquiv_iff a b (TwoSquare.mk _ _ _ _ l) r).2 h).symm

private theorem identity_exchange_of_units
    {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    {F : C ⥤ A} (R : D ⥤ A) (R' : D ⥤ B) (G E : A ⥤ B) (H : D ⥤ D)
    (u : F ⟶ Q ⋙ R) [R.IsRightDerivedFunctor u W] [E.IsLeftAdjoint]
    (ν : G ≅ E) (d : H ≅ 𝟭 D) (β : R ⋙ G ⟶ H ⋙ R') (θ : R ⋙ E ≅ R')
    (h : ∀ K, G.map (u.app K) ≫ β.app (Q.obj K) ≫ R'.map (d.hom.app (Q.obj K)) =
      ν.hom.app (F.obj K) ≫ E.map (u.app K) ≫ θ.hom.app (Q.obj K)) (K : D) :
    β.app K ≫ R'.map (d.hom.app K) = ν.hom.app (R.obj K) ≫ θ.hom.app K := by
  let ψ : R ⋙ E ⟶ R' := whiskerLeft R ν.inv ≫ β ≫ whiskerRight d.hom R' ≫
    (leftUnitor R').hom
  have he : ψ = θ.hom := by
    apply (R ⋙ E).rightDerived_ext
      (whiskerRight u E ≫ (Functor.associator _ _ _).hom) W R' ψ θ.hom
    ext X
    simp only [NatTrans.comp_app, whiskerRight_app, associator_hom_app,
      whiskerLeft_app, Category.comp_id, ψ, leftUnitor_hom_app]
    erw [Category.comp_id]
    have hn := ν.inv.naturality (u.app X)
    dsimp only [Functor.comp_obj] at hn
    rw [← Category.assoc, hn]
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
      congrArg (fun z => ν.inv.app (F.obj X) ≫ z) (h X)
  have heK := congrArg (fun t => ν.hom.app (R.obj K) ≫ t.app K) he
  simp only [ψ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    leftUnitor_hom_app, Iso.hom_inv_id_app_assoc] at heK
  erw [Category.comp_id] at heK
  exact heK

private theorem contract_identity_cube
    {A B A₀ A₁ D : Type*}
    [Category* A] [Category* B] [Category* A₀] [Category* A₁] [Category* D]
    (Q₀ : A ⥤ A₀) (Q₁ : A ⥤ A₁) (P : B ⥤ D)
    (R : B ⥤ A) (G : A ⥤ A) (H : B ⥤ B)
    (R₀ : D ⥤ A₀) (R₁ : D ⥤ A₁) (G' : A₀ ⥤ A₁) (H' : D ⥤ D)
    (u₀ : R ⋙ Q₀ ⟶ P ⋙ R₀) (u₁ : R ⋙ Q₁ ⟶ P ⋙ R₁)
    (β : R ⋙ G ⟶ H ⋙ R) (β' : R₀ ⋙ G' ⟶ H' ⋙ R₁)
    (γ : Q₀ ⋙ G' ≅ G ⋙ Q₁) (δ : P ⋙ H' ≅ H ⋙ P)
    (dG : G ≅ 𝟭 A) (dH : H ≅ 𝟭 B) (dH' : H' ≅ 𝟭 D)
    (hc : HorizontalMateCubeEquation u₀ u₁ β β' γ.hom δ.hom)
    (hb : ∀ K, β.app K ≫ R.map (dH.hom.app K) = dG.hom.app (R.obj K))
    (hd : ∀ K, dH'.hom.app (P.obj K) = δ.hom.app K ≫ P.map (dH.hom.app K))
    (K : B) :
    G'.map (u₀.app K) ≫ β'.app (P.obj K) ≫ R₁.map (dH'.hom.app (P.obj K)) =
      γ.hom.app (R.obj K) ≫ Q₁.map (dG.hom.app (R.obj K)) ≫ u₁.app K := by
  have hn := u₁.naturality (dH.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  calc
    _ = (G'.map (u₀.app K) ≫ β'.app (P.obj K) ≫ R₁.map (δ.hom.app K)) ≫
        R₁.map (P.map (dH.hom.app K)) := by
      rw [hd, R₁.map_comp]
      simp only [Category.assoc]
    _ = (γ.hom.app (R.obj K) ≫ Q₁.map (β.app K) ≫ u₁.app (H.obj K)) ≫
        R₁.map (P.map (dH.hom.app K)) := by rw [hc K]
    _ = _ := by
      simp only [Category.assoc]
      rw [← hn, ← Q₁.map_comp_assoc, hb]

universe u wM wS₀ wS₁

variable (Λ : Type (u + 1)) [Ring Λ]

private theorem ordinary_identity_square {M S : Scheme.{u}} (p : M ⟶ S)
    (e : p ≫ 𝟙 S = 𝟙 M ≫ p) :
    moduleInverseImageSquareIso Λ p p (𝟙 S) (𝟙 M) e ≪≫
        isoWhiskerLeft (moduleInverseImage p Λ) (moduleInverseImageIdIso Λ M) ≪≫
        rightUnitor (moduleInverseImage p Λ) =
      isoWhiskerRight (moduleInverseImageIdIso Λ S) (moduleInverseImage p Λ) ≪≫
        leftUnitor (moduleInverseImage p Λ) := by
  apply Iso.ext
  apply (cancel_epi (moduleInverseImageCompIso Λ (𝟙 S) p).hom).1
  simp only [moduleInverseImageSquareIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  have hA := congrArg Iso.hom (moduleInverseImageCompIso_id_comp Λ p)
  have hB := congrArg Iso.hom (moduleInverseImageCompIso_comp_id Λ p)
  simp only [Iso.trans_hom] at hA hB
  rw [hB, hA]
  simp only [eqToIso.hom, eqToHom_trans]

private theorem ordinary_identity_exchange {M S : Scheme.{u}} (p : M ⟶ S)
    (e : p ≫ 𝟙 S = 𝟙 M ≫ p) (F : ModuleSheaf M Λ) :
    (moduleBaseChangeMap Λ p p (𝟙 S) (𝟙 M) e).app F ≫
        (moduleDirectImage p Λ).map ((moduleInverseImageIdIso Λ M).hom.app F) =
      (moduleInverseImageIdIso Λ S).hom.app ((moduleDirectImage p Λ).obj F) := by
  have hα : ∀ A : ModuleSheaf S Λ,
      (moduleInverseImage p Λ).map ((moduleInverseImageIdIso Λ S).hom.app A) ≫
          (TwoSquare.hId (moduleInverseImage p Λ)).app A =
        (moduleInverseImageSquareIso Λ p p (𝟙 S) (𝟙 M) e).hom.app A ≫
          (moduleInverseImageIdIso Λ M).hom.app ((moduleInverseImage p Λ).obj A) := by
    intro A
    have he := congrArg (fun i => i.hom.app A) (ordinary_identity_square Λ p e)
    simpa [TwoSquare.hId] using he.symm
  have he := mateEquiv_top_bottom_naturality (moduleInverseImageAdjunction p Λ)
    (moduleInverseImageAdjunction p Λ)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ p p (𝟙 S) (𝟙 M) e).hom)
    (TwoSquare.hId (moduleInverseImage p Λ)) (moduleInverseImageIdIso Λ S).hom
    (moduleInverseImageIdIso Λ M).hom hα F
  simpa [moduleBaseChangeMap, mateEquiv_hId, TwoSquare.vId] using he.symm

variable (S : Scheme.{u})
  (hS₀ : HasDerivedCategory.{wS₀} (ModuleSheaf S Λ))
  (hS₁ : HasDerivedCategory.{wS₁} (ModuleSheaf S Λ))

/-- The original localization equivalence between the two specified base models. -/
abbrev moduleUnboundedBaseModelEquivalence :=
  Localization.uniq (@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₀)
    (@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₁)
    (HomologicalComplex.quasiIso (ModuleSheaf S Λ) (.up ℤ))

/-- The original full-complex identity factor between the two base models. -/
def moduleUnboundedDerivedInverseImageIdentityModelFactor :
    @DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₀ ⋙
        @moduleUnboundedDerivedInverseImage Λ _ S S (𝟙 S) hS₀ hS₁ ≅
      @DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₁ :=
  @Functor.mapDerivedCategoryFactors _ _ _ hS₀ _ _ _ hS₁
      (moduleInverseImage (𝟙 S) Λ) _ _ _ ≪≫
    isoWhiskerRight (NatIso.mapHomologicalComplex (moduleInverseImageIdIso Λ S) (.up ℤ))
      (@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₁) ≪≫
    isoWhiskerRight (Functor.mapHomologicalComplexIdIso _ (.up ℤ)) _ ≪≫ leftUnitor _

/-- The actual inverse image of the identity is the original localization transport. -/
def moduleUnboundedDerivedInverseImageIdentityModelIso :
    @moduleUnboundedDerivedInverseImage Λ _ S S (𝟙 S) hS₀ hS₁ ≅
      (moduleUnboundedBaseModelEquivalence Λ S hS₀ hS₁).functor :=
  Localization.isoUniqFunctor (@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₀)
    (@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₁)
    (HomologicalComplex.quasiIso (ModuleSheaf S Λ) (.up ℤ)) _
    (moduleUnboundedDerivedInverseImageIdentityModelFactor Λ S hS₀ hS₁)

/-- Identity inverse image retains its original full-complex localization factor. -/
@[reassoc]
theorem moduleUnboundedDerivedInverseImageIdentityModelIso_fac
    (K : CochainComplex (ModuleSheaf S Λ) ℤ) :
    (moduleUnboundedDerivedInverseImageIdentityModelIso Λ S hS₀ hS₁).hom.app
        ((@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₀).obj K) ≫
      (Localization.compUniqFunctor (@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₀)
        (@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₁)
        (HomologicalComplex.quasiIso (ModuleSheaf S Λ) (.up ℤ))).hom.app K =
    (@Functor.mapDerivedCategoryFactors _ _ _ hS₀ _ _ _ hS₁
        (moduleInverseImage (𝟙 S) Λ) _ _ _).hom.app K ≫
      (@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₁).map
        ((NatIso.mapHomologicalComplex (moduleInverseImageIdIso Λ S) (.up ℤ)).hom.app K) := by
  have h := Localization.isoUniqFunctor_hom_app_comp
    (@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₀)
    (@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₁)
    (HomologicalComplex.quasiIso (ModuleSheaf S Λ) (.up ℤ)) _
    (moduleUnboundedDerivedInverseImageIdentityModelFactor Λ S hS₀ hS₁) K
  have hi : (Functor.mapHomologicalComplexIdIso (ModuleSheaf S Λ) (.up ℤ)).hom.app K =
      𝟙 K := by
    ext n
    rfl
  simp only [moduleUnboundedDerivedInverseImageIdentityModelFactor,
    Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom,
    whiskerRight_app, leftUnitor_hom_app, hi] at h
  erw [(@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₁).map_id K,
    Category.id_comp, Category.comp_id] at h
  exact h

variable {S} {M : Scheme.{u}} (p : M ⟶ S)
  (hM : HasDerivedCategory.{wM} (ModuleSheaf M Λ))

/-- Original right-derived uniqueness transports only the base model, fixing the source. -/
abbrev moduleUnboundedDerivedDirectImageChangeBaseModel :
    @moduleUnboundedDerivedDirectImage Λ _ S M p hS₀ hM ⋙
        (moduleUnboundedBaseModelEquivalence Λ S hS₀ hS₁).functor ≅
      @moduleUnboundedDerivedDirectImage Λ _ S M p hS₁ hM :=
  (moduleDirectImage p Λ).unboundedRightDerivedFunctorChangeTarget hM hS₀ hS₁

/-- The base-model comparison preserves both actual right-derived units. -/
@[reassoc]
theorem moduleUnboundedDerivedDirectImageChangeBaseModel_unit
    (K : CochainComplex (ModuleSheaf M Λ) ℤ) :
    (moduleUnboundedBaseModelEquivalence Λ S hS₀ hS₁).functor.map
        ((@moduleUnboundedDerivedDirectImageUnit Λ _ S M p hS₀ hM).app K) ≫
      (moduleUnboundedDerivedDirectImageChangeBaseModel Λ hS₀ hS₁ p hM).hom.app
        ((@DerivedCategory.Q (ModuleSheaf M Λ) _ _ hM).obj K) =
    (Localization.compUniqFunctor (@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₀)
        (@DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₁)
        (HomologicalComplex.quasiIso (ModuleSheaf S Λ) (.up ℤ))).hom.app
        (((moduleDirectImage p Λ).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (@moduleUnboundedDerivedDirectImageUnit Λ _ S M p hS₁ hM).app K :=
  (moduleDirectImage p Λ).unboundedRightDerivedFunctorChangeTarget_unit hM hS₀ hS₁ K

local notation "Q₀" => @DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₀
local notation "Q₁" => @DerivedCategory.Q (ModuleSheaf S Λ) _ _ hS₁
local notation "QM" => @DerivedCategory.Q (ModuleSheaf M Λ) _ _ hM
local notation "R₀" => @moduleUnboundedDerivedDirectImage Λ _ S M p hS₀ hM
local notation "R₁" => @moduleUnboundedDerivedDirectImage Λ _ S M p hS₁ hM
local notation "GD" => @moduleUnboundedDerivedInverseImage Λ _ S S (𝟙 S) hS₀ hS₁
local notation "HD" => @moduleUnboundedDerivedInverseImage Λ _ M M (𝟙 M) hM hM
local notation "u₀" => @moduleUnboundedDerivedDirectImageUnit Λ _ S M p hS₀ hM
local notation "u₁" => @moduleUnboundedDerivedDirectImageUnit Λ _ S M p hS₁ hM
local notation "γ" => @Functor.mapDerivedCategoryFactors _ _ _ hS₀ _ _ _ hS₁
  (moduleInverseImage (𝟙 S) Λ) _ _ _
local notation "δ" => @Functor.mapDerivedCategoryFactors _ _ _ hM _ _ _ hM
  (moduleInverseImage (𝟙 M) Λ) _ _ _

variable (e : p ≫ 𝟙 S = 𝟙 M ≫ p)

local notation "β" => moduleBaseChangeMap Λ p p (𝟙 S) (𝟙 M) e
local notation "β'" => @moduleUnboundedDerivedBaseChangeMap Λ _ M S M S
  hM hS₀ hM hS₁ p p (𝟙 S) (𝟙 M) e

private theorem identity_base_unit_cube :
    HorizontalMateCubeEquation
      (G := (moduleInverseImage (𝟙 S) Λ).mapHomologicalComplex (.up ℤ))
      (H := (moduleInverseImage (𝟙 M) Λ).mapHomologicalComplex (.up ℤ))
      (G' := GD) (H' := HD)
      u₀ u₁ ((β).mapHomologicalComplex (.up ℤ)) β' (γ).hom (δ).hom := by
  let a := (moduleInverseImageAdjunction p Λ).mapHomologicalComplex (.up ℤ)
  let a₀ := @moduleUnboundedDerivedAdjunction Λ _ S M p hS₀ hM
  let a₁ := @moduleUnboundedDerivedAdjunction Λ _ S M p hS₁ hM
  let l₀ := @Functor.mapDerivedCategoryFactors _ _ _ hS₀ _ _ _ hM
    (moduleInverseImage p Λ) _ _ _
  let l₁ := @Functor.mapDerivedCategoryFactors _ _ _ hS₁ _ _ _ hM
    (moduleInverseImage p Λ) _ _ _
  exact horizontalMateCubeEquation_of_specified_mates
    (G := (moduleInverseImage (𝟙 S) Λ).mapHomologicalComplex (.up ℤ))
    (H := (moduleInverseImage (𝟙 M) Λ).mapHomologicalComplex (.up ℤ))
    (G' := GD) (H' := HD) a a a₀ a₁ l₀.hom l₁.hom
    ((moduleInverseImageSquareIso Λ p p (𝟙 S) (𝟙 M) e).hom.mapHomologicalComplex (.up ℤ))
    (@moduleUnboundedDerivedInverseImageSquareIso Λ _ M S M S
      hM hS₀ hM hS₁ p p (𝟙 S) (𝟙 M) e).hom (γ).hom (δ).hom
    u₀ u₁ ((β).mapHomologicalComplex (.up ℤ)) β'
    (factor_mate_of_counit a a₀ l₀.hom u₀
      (@moduleUnboundedDerivedAdjunction_counit_fac Λ _ S M p hS₀ hM))
    (factor_mate_of_counit a a₁ l₁.hom u₁
      (@moduleUnboundedDerivedAdjunction_counit_fac Λ _ S M p hS₁ hM))
    (mapHomologicalComplex_mate (moduleInverseImageAdjunction p Λ)
      (moduleInverseImageAdjunction p Λ)
      (moduleInverseImageSquareIso Λ p p (𝟙 S) (𝟙 M) e).hom β rfl (.up ℤ))
    rfl
    (@moduleUnboundedDerivedInverseImageSquareIso_pastingExactFactor Λ _ M S M S
      hM hS₀ hM hS₁ p p (𝟙 S) (𝟙 M) e)

private theorem identity_base_unit_contraction (K : CochainComplex (ModuleSheaf M Λ) ℤ) :
    (GD).map ((u₀).app K) ≫ (β').app ((QM).obj K) ≫
        (R₁).map ((@moduleUnboundedDerivedInverseImageIdIso Λ _ M hM).hom.app ((QM).obj K)) =
      (γ).hom.app (((moduleDirectImage p Λ).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (Q₁).map ((NatIso.mapHomologicalComplex (moduleInverseImageIdIso Λ S) (.up ℤ)).hom.app
          (((moduleDirectImage p Λ).mapHomologicalComplex (.up ℤ)).obj K)) ≫ (u₁).app K := by
  apply contract_identity_cube Q₀ Q₁ QM
    ((moduleDirectImage p Λ).mapHomologicalComplex (.up ℤ))
    ((moduleInverseImage (𝟙 S) Λ).mapHomologicalComplex (.up ℤ))
    ((moduleInverseImage (𝟙 M) Λ).mapHomologicalComplex (.up ℤ))
    R₀ R₁ GD HD u₀ u₁ ((β).mapHomologicalComplex (.up ℤ)) β' γ δ
    (NatIso.mapHomologicalComplex (moduleInverseImageIdIso Λ S) (.up ℤ))
    (NatIso.mapHomologicalComplex (moduleInverseImageIdIso Λ M) (.up ℤ))
    (@moduleUnboundedDerivedInverseImageIdIso Λ _ M hM)
    (identity_base_unit_cube Λ hS₀ hS₁ p hM e)
  · intro L
    ext n : 1
    exact ordinary_identity_exchange Λ p e (L.X n)
  · intro L
    let := hM
    exact Functor.mapDerivedCategoryOriginalIdIso_fac
      (moduleInverseImage (𝟙 M) Λ) (moduleInverseImageIdIso Λ M) L

/-- The original identity-base exchange, after the original source-identity contraction,
is exactly the inverse-image localization comparison followed by right-derived uniqueness.
The two base models remain independent; no properness or torsion hypothesis is used. -/
@[reassoc]
theorem moduleUnboundedDerivedBaseChangeMap_identity_baseModel
    (K : @DerivedCategory (ModuleSheaf M Λ) _ _ hM) :
    (β').app K ≫ (R₁).map ((@moduleUnboundedDerivedInverseImageIdIso Λ _ M hM).hom.app K) =
      (moduleUnboundedDerivedInverseImageIdentityModelIso Λ S hS₀ hS₁).hom.app ((R₀).obj K) ≫
        (moduleUnboundedDerivedDirectImageChangeBaseModel Λ hS₀ hS₁ p hM).hom.app K := by
  apply identity_exchange_of_units QM (HomologicalComplex.quasiIso (ModuleSheaf M Λ) (.up ℤ))
    R₀ R₁ GD (moduleUnboundedBaseModelEquivalence Λ S hS₀ hS₁).functor HD u₀
    (moduleUnboundedDerivedInverseImageIdentityModelIso Λ S hS₀ hS₁)
    (@moduleUnboundedDerivedInverseImageIdIso Λ _ M hM) β'
    (moduleUnboundedDerivedDirectImageChangeBaseModel Λ hS₀ hS₁ p hM) _ K
  intro L
  rw [identity_base_unit_contraction Λ hS₀ hS₁ p hM e,
    moduleUnboundedDerivedDirectImageChangeBaseModel_unit]
  simpa only [Functor.comp_obj, Functor.id_obj, Category.assoc] using
    (congrArg (fun t => t ≫ (u₁).app L)
    (moduleUnboundedDerivedInverseImageIdentityModelIso_fac Λ S hS₀ hS₁
      (((moduleDirectImage p Λ).mapHomologicalComplex (.up ℤ)).obj L))).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
