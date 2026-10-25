/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleSections

/-! # Original unit sections and coefficient maps on the base-changed chart

The native unit and chart-evaluation square is normalized before specializing
the coefficient sheaf. Its inverse-image square and coefficient morphism are
the original ones. No cohomological comparison or invertibility is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

private theorem coefficient_evaluation_paste {C D : Type*} [Category* C] [Category* D]
    (Γ : C ⥤ D) {A B E : C} {X Y Z T : D}
    (u : X ⟶ Y) (φ : Y ⟶ Z) (v : Y ⟶ Γ.obj B) (w : Z ⟶ Γ.obj E)
    (t : X ⟶ T) (p : T ⟶ Γ.obj A) (a : A ⟶ B) (b : B ⟶ E)
    (hu : u ≫ v = t ≫ p ≫ Γ.map a) (hn : φ ≫ w = v ≫ Γ.map b) :
    u ≫ φ ≫ w = (t ≫ p) ≫ Γ.map (a ≫ b) := by
  calc
    _ = u ≫ v ≫ Γ.map b := by rw [hn]
    _ = (u ≫ v) ≫ Γ.map b := (Category.assoc _ _ _).symm
    _ = (t ≫ p ≫ Γ.map a) ≫ Γ.map b := by rw [hu]
    _ = _ := by rw [Γ.map_comp]; simp only [Category.assoc]

private theorem coefficient_evaluation_of_whole
    {C C' E E' A : Type*} [Category* C] [Category* C']
    [Category* E] [Category* E'] [Category* A]
    (G : C ⥤ C') (I : C ⥤ E) (J : C' ⥤ E') (B : E ⥤ E')
    (Λ : E ⥤ A) (Γ : E' ⥤ A) (sourceValues : C ⥤ A) (Τ : C' ⥤ A)
    (eU : I ⋙ Λ ≅ sourceValues) (eV : J ⋙ Γ ≅ Τ) (s : Λ ⟶ B ⋙ Γ)
    (δ : I ⋙ B ⟶ G ⋙ J) (unit : sourceValues ⟶ G ⋙ Τ)
    (square : I ⋙ Λ ⟶ G ⋙ J ⋙ Γ)
    (hsquare : square = Functor.whiskerLeft I s ≫ Functor.whiskerRight δ Γ)
    (hunit : unit ≫ Functor.whiskerLeft G eV.inv = eU.inv ≫ square)
    (X : C) (Y : C') (φ : G.obj X ⟶ Y)
    (EU : Λ.obj (I.obj X) ≅ sourceValues.obj X) (EV : Γ.obj (J.obj Y) ≅ Τ.obj Y)
    (u : sourceValues.obj X ⟶ Τ.obj (G.obj X)) (k : Τ.obj (G.obj X) ⟶ Τ.obj Y)
    (p : Λ.obj (I.obj X) ⟶ Γ.obj (B.obj (I.obj X)))
    (hEU : eU.app X = EU) (hEV : eV.app Y = EV)
    (hu : unit.app X = u) (hk : Τ.map φ = k) (hp : s.app (I.obj X) = p) :
    u ≫ k ≫ EV.inv = (EU.inv ≫ p) ≫ Γ.map (δ.app X ≫ J.map φ) := by
  subst EU
  subst EV
  subst u
  subst k
  subst p
  have h : unit.app X ≫ eV.inv.app (G.obj X) =
      eU.inv.app X ≫ s.app (I.obj X) ≫ Γ.map (δ.app X) := by
    rw [hsquare] at hunit
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] using NatTrans.congr_app hunit X
  exact coefficient_evaluation_paste Γ (unit.app X) (Τ.map φ)
    (eV.inv.app (G.obj X)) (eV.inv.app Y) (eU.inv.app X) (s.app (I.obj X))
    (δ.app X) (J.map φ) h (eV.inv.naturality φ)

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

private theorem squareSectionsNatTrans_arrow_congr {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (fT : Y ⟶ T) (g : T ⟶ S) (r₁ r₂ : Y ⟶ X)
    (h₁ : fT ≫ g = r₁ ≫ f) (h₂ : fT ≫ g = r₂ ≫ f) (hr : r₁ = r₂) :
    Continuity.squareSectionsNatTrans f fT g r₁ h₁ =
      Continuity.squareSectionsNatTrans f fT g r₂ h₂ := by
  subst r₂
  rfl

private theorem unitRepresentativeArrow_identity {S T : Scheme.{u}}
    (g : T ⟶ S) (U : S.Etale) :
    (Continuity.unitRepresentativeArrow g (𝟙 ((siteBaseChange g).obj U))).left =
      pullback.fst U.hom g := by
  let V : T.Etale := (siteBaseChange g).obj U
  let b : V.left ⟶ U.left := pullback.fst U.hom g
  exact (congrArg (fun k : V.left ⟶ V.left => k ≫ b)
    (etaleHom_id_left V)).trans (Category.id_comp b)

private theorem unitSectionMap_identity {S T : Scheme.{u}}
    (g : T ⟶ S) (U : S.Etale) (L : AbelianSheaf.{u, u + 1} S) :
    Continuity.unitSectionMap g L (𝟙 ((siteBaseChange g).obj U)) =
      ((inverseImageAdjunction g).unit.app L).hom.app (op U) := by
  let V : T.Etale := (siteBaseChange g).obj U
  let P := ((inverseImage g).obj L).obj
  let u := ((inverseImageAdjunction g).unit.app L).hom.app (op U)
  have hid : P.map (𝟙 V).op = 𝟙 (P.obj (op V)) := by
    simpa only [op_id] using P.map_id (op V)
  change u ≫ P.map (𝟙 V).op = u
  exact (congrArg (fun k => u ≫ k) hid).trans (Category.comp_id u)

private theorem unitSectionNatTrans_baseChangeChart_square {S T : Scheme.{u}}
    (g : T ⟶ S) (U : S.Etale) :
    Continuity.unitSectionNatTrans g (𝟙 ((siteBaseChange g).obj U)) ≫
        Functor.whiskerLeft (inverseImage g)
          (Continuity.pullbackSectionsEtaleEvaluationNatIso ((siteBaseChange g).obj U)).inv =
      (Continuity.pullbackSectionsEtaleEvaluationNatIso U).inv ≫
        Continuity.squareSectionsNatTrans U.hom ((siteBaseChange g).obj U).hom g
          (pullback.fst U.hom g) pullback.condition.symm := by
  let V : T.Etale := (siteBaseChange g).obj U
  let b : V.left ⟶ U.left := pullback.fst U.hom g
  let a := Continuity.unitRepresentativeArrow g (𝟙 V)
  have hs := squareSectionsNatTrans_arrow_congr U.hom V.hom g a.left b
    (Over.w a).symm pullback.condition.symm (unitRepresentativeArrow_identity g U)
  exact (Continuity.unitSectionNatTrans_square g (𝟙 V)).trans
    (congrArg (fun t => (Continuity.pullbackSectionsEtaleEvaluationNatIso U).inv ≫ t) hs)

/-- The original unit followed by an arbitrary original coefficient map, after
chart evaluation, is exactly its original coefficient-square section transfer. -/
theorem unitSectionMap_baseChangeChart_coefficient {S T : Scheme.{u}}
    (g : T ⟶ S) (U : S.Etale)
    {L : AbelianSheaf.{u, u + 1} S} {M : AbelianSheaf.{u, u + 1} T}
    (φ : (inverseImage g).obj L ⟶ M) :
    ((inverseImageAdjunction g).unit.app L).hom.app (op U) ≫
        φ.hom.app (op ((siteBaseChange g).obj U)) ≫
        (Continuity.pullbackSectionsEtaleEvaluationIso M ((siteBaseChange g).obj U)).inv =
      ((Continuity.pullbackSectionsEtaleEvaluationIso L U).inv ≫
        globalSectionsPullback (pullback.fst U.hom g) ((inverseImage U.hom).obj L)) ≫
        (globalSections ((siteBaseChange g).obj U).left).map
          ((inverseImageSquareIso U.hom ((siteBaseChange g).obj U).hom g
            (pullback.fst U.hom g) pullback.condition.symm).inv.app L ≫
            (inverseImage ((siteBaseChange g).obj U).hom).map φ) := by
  let V : T.Etale := (siteBaseChange g).obj U
  let b : V.left ⟶ U.left := pullback.fst U.hom g
  exact coefficient_evaluation_of_whole
    (inverseImage g) (inverseImage U.hom) (inverseImage V.hom) (inverseImage b)
    (globalSections U.left) (globalSections V.left)
    ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U))
    ((sheafSections T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V))
    (Continuity.pullbackSectionsEtaleEvaluationNatIso U)
    (Continuity.pullbackSectionsEtaleEvaluationNatIso V)
    (globalSectionsPullbackNatTrans b)
    (inverseImageSquareIso U.hom V.hom g b pullback.condition.symm).inv
    (Continuity.unitSectionNatTrans g (𝟙 V))
    (Continuity.squareSectionsNatTrans U.hom V.hom g b pullback.condition.symm)
    rfl (unitSectionNatTrans_baseChangeChart_square g U) L M φ
    (Continuity.pullbackSectionsEtaleEvaluationIso L U)
    (Continuity.pullbackSectionsEtaleEvaluationIso M V)
    (((inverseImageAdjunction g).unit.app L).hom.app (op U))
    (φ.hom.app (op V)) (globalSectionsPullback b ((inverseImage U.hom).obj L))
    rfl rfl
    ((Continuity.unitSectionNatTrans_app g (𝟙 V) L).trans (unitSectionMap_identity g U L))
    rfl rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
