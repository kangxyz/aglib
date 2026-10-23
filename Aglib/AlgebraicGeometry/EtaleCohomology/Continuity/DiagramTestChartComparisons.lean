/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleTest
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramRightTail

/-! # Original chart and triangle comparisons for the direct test-section argument

These are native chart evaluation, pullback-symmetry and right-tail component
formulas. They do not specialize a pulled coefficient system and do not assert
any section-colimit or coefficient-colimit certificate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u uI vI

attribute [local instance] hasSheafifyLarge

/-- The original site composition comparison with the specified triangle transport. -/
def siteBaseChangeTriangleIso {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (p : Z ⟶ X) (q : Z ⟶ Y) (h : q ≫ f = p) :
    siteBaseChange p ≅ siteBaseChange f ⋙ siteBaseChange q :=
  eqToIso (congrArg siteBaseChange h.symm) ≪≫ siteBaseChangeComp f q

@[reassoc]
lemma siteBaseChangeTriangleIso_hom_fst_fst {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (p : Z ⟶ X) (q : Z ⟶ Y) (h : q ≫ f = p) (T : X.Etale) :
    ((siteBaseChangeTriangleIso f p q h).hom.app T).left ≫
      pullback.fst (pullback.snd T.hom f) q ≫ pullback.fst T.hom f =
        pullback.fst T.hom p := by
  subst p
  simpa only [siteBaseChangeTriangleIso, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, eqToHom_refl, Category.id_comp] using
      siteBaseChangeComp_hom_fst_fst f q T

@[reassoc]
lemma siteBaseChangeTriangleIso_hom_fst_snd {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (p : Z ⟶ X) (q : Z ⟶ Y) (h : q ≫ f = p) (T : X.Etale) :
    ((siteBaseChangeTriangleIso f p q h).hom.app T).left ≫
      pullback.fst (pullback.snd T.hom f) q ≫ pullback.snd T.hom f =
        pullback.snd T.hom p ≫ q := by
  subst p
  simpa only [siteBaseChangeTriangleIso, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, eqToHom_refl, Category.id_comp] using
      siteBaseChangeComp_hom_fst_snd f q T

/-- The direct-image triangle acts by the original contravariant site triangle. -/
lemma directImageTriangleIso_component {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (p : Z ⟶ X) (q : Z ⟶ Y) (h : q ≫ f = p)
    (F : AbelianSheaf.{u, u + 1} Z) (T : X.Etale) :
    ((directImageTriangleIso f p q h).hom.app F).hom.app (op T) =
      F.obj.map ((siteBaseChangeTriangleIso f p q h).hom.app T).op := by
  subst p
  change (𝟙 _ ≫ F.obj.map ((siteBaseChangeComp f q).hom.app T).op) ≫ 𝟙 _ =
    F.obj.map (𝟙 _ ≫ (siteBaseChangeComp f q).hom.app T).op
  simp only [Category.id_comp, Category.comp_id]

/-- Rebase the actual test arrow without changing the original coefficient-square map. -/
lemma squareSectionsMap_etaleEvaluation_of_left {X S : Scheme.{u}} (f : S ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} S}
    (φ : (inverseImage f).obj F ⟶ G) {U : X.Etale} {W : S.Etale}
    (a : W ⟶ (siteBaseChange f).obj U) (r : W.left ⟶ U.left)
    (hr : r = (unitRepresentativeArrow f a).left) (e : W.hom ≫ f = r ≫ U.hom) :
    squareSectionsMap (X₀ := U.left) (S₀ := X) (X₁ := W.left) (S₁ := S)
        U.hom W.hom f r e φ ≫ (pullbackSectionsEtaleEvaluationIso G W).hom =
      (pullbackSectionsEtaleEvaluationIso F U).hom ≫
        ((inverseImageAdjunction f).homEquiv _ _ φ).hom.app (op U) ≫ G.obj.map a.op := by
  subst r
  exact squareSectionsMap_etaleEvaluation f φ a

/-- Naturality of a presheaf coefficient transition across the two original chart isomorphisms. -/
lemma presheafTransition_chartIso {C D : Type*} [Category* C] [Category* D]
    {A : Type*} [Category* A] (K : C ⥤ D) (P : Cᵒᵖ ⥤ A) (Q : Dᵒᵖ ⥤ A)
    (η : P ⟶ K.op ⋙ Q) {U U' : C} {V V' : D}
    (e : U ≅ U') (e' : V ≅ V') (c : V' ⟶ K.obj U') (a : V ⟶ K.obj U)
    (ha : e'.inv ≫ a = c ≫ K.map e.inv) :
    η.app (op U) ≫ Q.map a.op ≫ Q.map e'.inv.op =
      P.map e.inv.op ≫ η.app (op U') ≫ Q.map c.op := by
  have hm : Q.map a.op ≫ Q.map e'.inv.op = Q.map ((K.map e.inv).op) ≫ Q.map c.op :=
    (Q.map_comp _ _).symm.trans
      ((congrArg (fun f => Q.map f.op) ha).trans (Q.map_comp _ _))
  have hn : η.app (op U) ≫ Q.map ((K.map e.inv).op) =
      P.map e.inv.op ≫ η.app (op U') := (η.naturality e.inv.op).symm
  exact (congrArg (fun f => η.app (op U) ≫ f) hm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ Q.map c.op) hn).trans (Category.assoc _ _ _)))

/-- Original square transfer, expressed in two specified isomorphic test charts. -/
lemma squareSectionsMap_chartIso {X S : Scheme.{u}} (f : S ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} S}
    (ψ : F ⟶ (directImage f).obj G) {U U' : X.Etale} {W W' : S.Etale}
    (eU : U ≅ U') (eW : W ≅ W') (c : W' ⟶ (siteBaseChange f).obj U')
    (a : W ⟶ (siteBaseChange f).obj U)
    (ha : eW.inv ≫ a = c ≫ (siteBaseChange f).map eU.inv)
    (r : W.left ⟶ U.left) (hr : r = (unitRepresentativeArrow f a).left)
    (h : W.hom ≫ f = r ≫ U.hom) :
    squareSectionsMap U.hom W.hom f r h
        (((inverseImageAdjunction f).homEquiv _ _).symm ψ) ≫
        ((pullbackSectionsEtaleEvaluationIso G W).hom ≫ G.obj.map eW.inv.op) =
      ((pullbackSectionsEtaleEvaluationIso F U).hom ≫ F.obj.map eU.inv.op) ≫
        ψ.hom.app (op U') ≫ G.obj.map c.op := by
  let φ : (inverseImage f).obj F ⟶ G :=
    ((inverseImageAdjunction f).homEquiv _ _).symm ψ
  have hψ : (inverseImageAdjunction f).homEquiv _ _ φ = ψ :=
    Equiv.apply_symm_apply _ _
  have he : squareSectionsMap U.hom W.hom f r h φ ≫
      (pullbackSectionsEtaleEvaluationIso G W).hom =
        (pullbackSectionsEtaleEvaluationIso F U).hom ≫
          ψ.hom.app (op U) ≫ G.obj.map a.op :=
    (squareSectionsMap_etaleEvaluation_of_left f φ a r hr h).trans
      (congrArg (fun η : F ⟶ (directImage f).obj G =>
        (pullbackSectionsEtaleEvaluationIso F U).hom ≫
        η.hom.app (op U) ≫ G.obj.map a.op) hψ)
  have hn := presheafTransition_chartIso (siteBaseChange f) F.obj G.obj ψ.hom
    eU eW c a ha
  calc
    squareSectionsMap U.hom W.hom f r h φ ≫
        ((pullbackSectionsEtaleEvaluationIso G W).hom ≫ G.obj.map eW.inv.op) =
      (squareSectionsMap U.hom W.hom f r h φ ≫
        (pullbackSectionsEtaleEvaluationIso G W).hom) ≫ G.obj.map eW.inv.op :=
      (Category.assoc _ _ _).symm
    _ = ((pullbackSectionsEtaleEvaluationIso F U).hom ≫
        ψ.hom.app (op U) ≫ G.obj.map a.op) ≫ G.obj.map eW.inv.op :=
      congrArg (fun z => z ≫ G.obj.map eW.inv.op) he
    _ = (pullbackSectionsEtaleEvaluationIso F U).hom ≫
        (ψ.hom.app (op U) ≫ G.obj.map a.op ≫ G.obj.map eW.inv.op) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => (pullbackSectionsEtaleEvaluationIso F U).hom ≫ z)
          (Category.assoc (ψ.hom.app (op U)) (G.obj.map a.op) (G.obj.map eW.inv.op)))
    _ = (pullbackSectionsEtaleEvaluationIso F U).hom ≫
        (F.obj.map eU.inv.op ≫ ψ.hom.app (op U') ≫ G.obj.map c.op) :=
      congrArg (fun z => (pullbackSectionsEtaleEvaluationIso F U).hom ≫ z) hn
    _ = _ := (Category.assoc _ _ _).symm

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (i : I) (T : (X.obj i).unop.Etale)

/-- The original under-category equation, with its native scheme orientation. -/
lemma diagramEtaleTest_triangle {a b : Under i} (m : a ⟶ b) :
    (X.map m.right).unop ≫ (X.map a.hom).unop = (X.map b.hom).unop :=
  Over.w (((relativeSchemeTail X i).map m).unop)

@[reassoc]
lemma diagramEtaleTestChartIso_hom_fst (a : Under i) :
    (diagramEtaleTestChartIso X i T a).hom.left ≫ pullback.fst T.hom (X.map a.hom).unop =
      pullback.snd (X.map a.hom).unop T.hom :=
  pullbackSymmetry_hom_comp_fst _ _

@[reassoc]
lemma diagramEtaleTestChartIso_hom_snd (a : Under i) :
    (diagramEtaleTestChartIso X i T a).hom.left ≫ pullback.snd T.hom (X.map a.hom).unop =
      pullback.fst (X.map a.hom).unop T.hom :=
  pullbackSymmetry_hom_comp_snd _ _

@[reassoc]
lemma diagramEtaleTestChartIso_inv_fst (a : Under i) :
    (diagramEtaleTestChartIso X i T a).inv.left ≫ pullback.fst (X.map a.hom).unop T.hom =
      pullback.snd T.hom (X.map a.hom).unop :=
  pullbackSymmetry_inv_comp_fst _ _

@[reassoc]
lemma diagramEtaleTestChartIso_inv_snd (a : Under i) :
    (diagramEtaleTestChartIso X i T a).inv.left ≫ pullback.snd (X.map a.hom).unop T.hom =
      pullback.fst T.hom (X.map a.hom).unop :=
  pullbackSymmetry_inv_comp_snd _ _

/-- The actual test morphism, expressed through the original site triangle and symmetry isos. -/
def diagramEtaleTestArrow {a b : Under i} (m : a ⟶ b) :
    diagramEtaleTestChart X i T b ⟶
      (siteBaseChange (X.map m.right).unop).obj (diagramEtaleTestChart X i T a) :=
  (diagramEtaleTestChartIso X i T b).hom ≫
    (siteBaseChangeTriangleIso (X.map a.hom).unop (X.map b.hom).unop
      (X.map m.right).unop (diagramEtaleTest_triangle X i m)).hom.app T ≫
    (siteBaseChange (X.map m.right).unop).map (diagramEtaleTestChartIso X i T a).inv

/-- The representative arrow of that original test morphism is the native test transition. -/
lemma diagramEtaleTestArrow_left {a b : Under i} (m : a ⟶ b) :
    (unitRepresentativeArrow (X.map m.right).unop (diagramEtaleTestArrow X i T m)).left =
      ((diagramEtaleTest X i T).map m).unop := by
  apply pullback.hom_ext
  · exact (Over.w (unitRepresentativeArrow (X.map m.right).unop
      (diagramEtaleTestArrow X i T m))).trans (diagramEtaleTest_map_fst X i T m).symm
  · let ε : pullback (X.map b.hom).unop T.hom ⟶
        pullback T.hom (X.map b.hom).unop := (diagramEtaleTestChartIso X i T b).hom.left
    let τ : pullback T.hom (X.map b.hom).unop ⟶
        pullback (pullback.snd T.hom (X.map a.hom).unop) (X.map m.right).unop :=
      ((siteBaseChangeTriangleIso (X.map a.hom).unop (X.map b.hom).unop
        (X.map m.right).unop (diagramEtaleTest_triangle X i m)).hom.app T).left
    let μ : pullback (pullback.snd T.hom (X.map a.hom).unop) (X.map m.right).unop ⟶
        pullback (diagramEtaleTestChart X i T a).hom (X.map m.right).unop :=
      ((siteBaseChange (X.map m.right).unop).map (diagramEtaleTestChartIso X i T a).inv).left
    let ρ := pullback.fst (diagramEtaleTestChart X i T a).hom (X.map m.right).unop
    let σ := pullback.snd (X.map a.hom).unop T.hom
    let π := pullback.fst (pullback.snd T.hom (X.map a.hom).unop) (X.map m.right).unop
    have hm : μ ≫ ρ ≫ σ = π ≫ pullback.fst T.hom (X.map a.hom).unop :=
      (Category.assoc μ ρ σ).symm.trans
        ((congrArg (fun z => z ≫ σ)
          (siteBaseChange_map_fst (X.map m.right).unop
            (diagramEtaleTestChartIso X i T a).inv)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun z => π ≫ z) (diagramEtaleTestChartIso_inv_snd X i T a))))
    have ht : τ ≫ π ≫ pullback.fst T.hom (X.map a.hom).unop =
        pullback.fst T.hom (X.map b.hom).unop :=
      siteBaseChangeTriangleIso_hom_fst_fst (X.map a.hom).unop (X.map b.hom).unop
        (X.map m.right).unop (diagramEtaleTest_triangle X i m) T
    have he : ε ≫ pullback.fst T.hom (X.map b.hom).unop =
        pullback.snd (X.map b.hom).unop T.hom := diagramEtaleTestChartIso_hom_fst X i T b
    change ((ε ≫ τ ≫ μ) ≫ ρ) ≫ σ = _
    exact (Category.assoc _ _ _).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => ε ≫ z) (Category.assoc τ μ (ρ ≫ σ))).trans
          ((congrArg (fun z => ε ≫ τ ≫ z) hm).trans
            ((congrArg (fun z => ε ≫ z) ht).trans
              (he.trans (diagramEtaleTest_map_snd X i T m).symm)))))

/-- The native right-tail transition is the original coefficient map and direct-image triangle. -/
lemma diagramRightTailTransition_triangle {j k l : I}
    (a : j ⟶ k) (b : k ⟶ l) (t : j ⟶ l) (h : a ≫ b = t) :
    InjectiveSystem.System.rightTailTransition (diagramAdjunctionData X) F a b t h =
      (directImage (X.map a).unop).map (F.map b) ≫
        (directImageTriangleIso (X.map a).unop (X.map t).unop (X.map b).unop
          ((congrArg Quiver.Hom.unop (X.map_comp a b)).symm.trans
            (congrArg (fun s => (X.map s).unop) h))).hom.app (F.obj l) := by
  subst t
  have hm := NatTrans.congr_app (diagramDirectImageComp_inv X a b) (F.obj l)
  simp only [NatTrans.comp_app, eqToHom_app] at hm
  change ((directImage (X.map a).unop).map (F.map b) ≫
      ((diagramAdjunctionData X).compIso a b).inv.app (F.obj l)) ≫ 𝟙 _ = _
  have hm' : ((diagramAdjunctionData X).compIso a b).inv.app (F.obj l) =
      (directImageTriangleIso (X.map a).unop (X.map (a ≫ b)).unop (X.map b).unop
        (congrArg Quiver.Hom.unop (X.map_comp a b)).symm).hom.app (F.obj l) := by
    simpa only [directImageTriangleIso, Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app] using hm
  exact (Category.comp_id _).trans
    (congrArg (fun q => (directImage (X.map a).unop).map (F.map b) ≫ q) hm')

/-- At a test object the tail map is the original coefficient component and restriction. -/
lemma diagramRightTail_map_component {a b : Under i} (m : a ⟶ b) :
    ((diagramRightTail X F i).map m).hom.app (op T) =
      (F.map m.right).hom.app (op ((siteBaseChange (X.map a.hom).unop).obj T)) ≫
        (F.obj b.right).obj.map
          ((siteBaseChangeTriangleIso (X.map a.hom).unop (X.map b.hom).unop
            (X.map m.right).unop (diagramEtaleTest_triangle X i m)).hom.app T).op := by
  have h := congrArg
    (fun q : (directImage (X.map a.hom).unop).obj (F.obj a.right) ⟶
        (directImage (X.map b.hom).unop).obj (F.obj b.right) => q.hom.app (op T))
    (diagramRightTailTransition_triangle X F a.hom m.right b.hom (Under.w m))
  exact h.trans (congrArg
    (fun q => (F.map m.right).hom.app
      (op ((siteBaseChange (X.map a.hom).unop).obj T)) ≫ q)
    (directImageTriangleIso_component (X.map a.hom).unop (X.map b.hom).unop
      (X.map m.right).unop (diagramEtaleTest_triangle X i m) (F.obj b.right) T))

/-- The test-arrow expression retains the original site-comparison triangle. -/
lemma diagramEtaleTestArrow_chartIso {a b : Under i} (m : a ⟶ b) :
    (diagramEtaleTestChartIso X i T b).inv ≫ diagramEtaleTestArrow X i T m =
      (siteBaseChangeTriangleIso (X.map a.hom).unop (X.map b.hom).unop
        (X.map m.right).unop (diagramEtaleTest_triangle X i m)).hom.app T ≫
        (siteBaseChange (X.map m.right).unop).map (diagramEtaleTestChartIso X i T a).inv := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫
      ((siteBaseChangeTriangleIso (X.map a.hom).unop (X.map b.hom).unop
        (X.map m.right).unop (diagramEtaleTest_triangle X i m)).hom.app T ≫
        (siteBaseChange (X.map m.right).unop).map
          (diagramEtaleTestChartIso X i T a).inv))
      (diagramEtaleTestChartIso X i T b).inv_hom_id).trans (Category.id_comp _))

/-- Original chart sections are the actual fixed-stage right-tail value. -/
def diagramTestChartSectionsIso (a : Under i) :
    (globalSections (diagramEtaleTestChart X i T a).left).obj
      ((inverseImage (diagramEtaleTestChart X i T a).hom).obj (F.obj a.right)) ≅
        ((diagramRightTail X F i).obj a).obj.obj (op T) :=
  pullbackSectionsEtaleEvaluationIso (F.obj a.right) (diagramEtaleTestChart X i T a) ≪≫
    (F.obj a.right).obj.mapIso (diagramEtaleTestChartIso X i T a).symm.op

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
