/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestChartComparisons

/-! # The original test-square leg and the evaluated right-tail leg

The native limit chart is compared with the original site base change by
pullback symmetry. The resulting section-square leg is the adjoint of the
original coefficient insertion, with the original right-image triangle.
The actual apex comparison is evaluation along that chart isomorphism;
no coefficient-colimit transport or continuity certificate is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u uI vI

attribute [local instance] hasSheafifyLarge

/-- Cancel the adjunction round trip before specializing a coefficient or a limit diagram. -/
lemma squareSectionsMap_chartIso_coefficient {Y S : Scheme.{u}} (f : S ⟶ Y)
    {P : AbelianSheaf.{u, u + 1} Y} {Q : AbelianSheaf.{u, u + 1} S}
    (φ : (inverseImage f).obj P ⟶ Q) {U U' : Y.Etale} {W W' : S.Etale}
    (eU : U ≅ U') (eW : W ≅ W') (t : W' ⟶ (siteBaseChange f).obj U')
    (a : W ⟶ (siteBaseChange f).obj U)
    (ha : eW.inv ≫ a = t ≫ (siteBaseChange f).map eU.inv)
    (r : W.left ⟶ U.left) (hr : r = (unitRepresentativeArrow f a).left)
    (h : W.hom ≫ f = r ≫ U.hom) :
    squareSectionsMap U.hom W.hom f r h φ ≫
        ((pullbackSectionsEtaleEvaluationIso Q W).hom ≫ Q.obj.map eW.inv.op) =
      ((pullbackSectionsEtaleEvaluationIso P U).hom ≫ P.obj.map eU.inv.op) ≫
        ((inverseImageAdjunction f).homEquiv _ _ φ).hom.app (op U') ≫ Q.obj.map t.op := by
  have hφ := ((inverseImageAdjunction f).homEquiv P Q).symm_apply_apply φ
  have hs := squareSectionsMap_chartIso f ((inverseImageAdjunction f).homEquiv P Q φ)
    eU eW t a ha r hr h
  exact (congrArg (fun q : (inverseImage f).obj P ⟶ Q =>
    squareSectionsMap U.hom W.hom f r h q ≫
      ((pullbackSectionsEtaleEvaluationIso Q W).hom ≫ Q.obj.map eW.inv.op)) hφ).symm.trans hs

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (i : I) (T : (X.obj i).unop.Etale) (c : Cocone X)

@[reassoc]
lemma diagramEtaleTest_cocone_fst (a : Under i) :
    ((diagramEtaleTestCocone X i T c).ι.app a).unop ≫
        pullback.fst (X.map a.hom).unop T.hom =
      pullback.fst (c.ι.app i).unop T.hom ≫ (c.ι.app a.right).unop :=
  congrArg Quiver.Hom.unop (diagramEtaleTestProjection_cocone X i T c a)

@[reassoc]
lemma diagramEtaleTest_cocone_snd (a : Under i) :
    ((diagramEtaleTestCocone X i T c).ι.app a).unop ≫
        pullback.snd (X.map a.hom).unop T.hom =
      pullback.snd (c.ι.app i).unop T.hom :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma diagramEtaleTestLimitChartIso_hom_fst :
    (diagramEtaleTestLimitChartIso X i T c).hom.left ≫
        pullback.fst T.hom (c.ι.app i).unop =
      pullback.snd (c.ι.app i).unop T.hom :=
  pullbackSymmetry_hom_comp_fst _ _

@[reassoc]
lemma diagramEtaleTestLimitChartIso_hom_snd :
    (diagramEtaleTestLimitChartIso X i T c).hom.left ≫
        pullback.snd T.hom (c.ι.app i).unop =
      pullback.fst (c.ι.app i).unop T.hom :=
  pullbackSymmetry_hom_comp_snd _ _

/-- The native limit chart maps to the original base change of each stage chart. -/
def diagramEtaleTestConeArrow (a : Under i) :
    diagramEtaleTestLimitChart X i T c ⟶
      (siteBaseChange (c.ι.app a.right).unop).obj (diagramEtaleTestChart X i T a) :=
  (diagramEtaleTestLimitChartIso X i T c).hom ≫
    (siteBaseChangeTriangleIso (X.map a.hom).unop (c.ι.app i).unop
      (c.ι.app a.right).unop (coneSquare X c a.hom)).hom.app T ≫
    (siteBaseChange (c.ι.app a.right).unop).map (diagramEtaleTestChartIso X i T a).inv

/-- Its representative is the actual native test-cocone leg. -/
lemma diagramEtaleTestConeArrow_left (a : Under i) :
    (unitRepresentativeArrow (c.ι.app a.right).unop
      (diagramEtaleTestConeArrow X i T c a)).left =
        ((diagramEtaleTestCocone X i T c).ι.app a).unop := by
  apply pullback.hom_ext
  · exact (Over.w (unitRepresentativeArrow (c.ι.app a.right).unop
      (diagramEtaleTestConeArrow X i T c a))).trans (diagramEtaleTest_cocone_fst X i T c a).symm
  · let ε : pullback (c.ι.app i).unop T.hom ⟶
        pullback T.hom (c.ι.app i).unop := (diagramEtaleTestLimitChartIso X i T c).hom.left
    let τ : pullback T.hom (c.ι.app i).unop ⟶
        pullback (pullback.snd T.hom (X.map a.hom).unop) (c.ι.app a.right).unop :=
      ((siteBaseChangeTriangleIso (X.map a.hom).unop (c.ι.app i).unop
        (c.ι.app a.right).unop (coneSquare X c a.hom)).hom.app T).left
    let μ : pullback (pullback.snd T.hom (X.map a.hom).unop) (c.ι.app a.right).unop ⟶
        pullback (diagramEtaleTestChart X i T a).hom (c.ι.app a.right).unop :=
      ((siteBaseChange (c.ι.app a.right).unop).map (diagramEtaleTestChartIso X i T a).inv).left
    let ρ := pullback.fst (diagramEtaleTestChart X i T a).hom (c.ι.app a.right).unop
    let σ := pullback.snd (X.map a.hom).unop T.hom
    let π := pullback.fst (pullback.snd T.hom (X.map a.hom).unop) (c.ι.app a.right).unop
    have hm : μ ≫ ρ ≫ σ = π ≫ pullback.fst T.hom (X.map a.hom).unop :=
      (Category.assoc μ ρ σ).symm.trans
        ((congrArg (fun z => z ≫ σ)
          (siteBaseChange_map_fst (c.ι.app a.right).unop
            (diagramEtaleTestChartIso X i T a).inv)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun z => π ≫ z) (diagramEtaleTestChartIso_inv_snd X i T a))))
    have ht : τ ≫ π ≫ pullback.fst T.hom (X.map a.hom).unop =
        pullback.fst T.hom (c.ι.app i).unop :=
      siteBaseChangeTriangleIso_hom_fst_fst (X.map a.hom).unop (c.ι.app i).unop
        (c.ι.app a.right).unop (coneSquare X c a.hom) T
    have he : ε ≫ pullback.fst T.hom (c.ι.app i).unop =
        pullback.snd (c.ι.app i).unop T.hom := diagramEtaleTestLimitChartIso_hom_fst X i T c
    change ((ε ≫ τ ≫ μ) ≫ ρ) ≫ σ = _
    exact (Category.assoc _ _ _).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => ε ≫ z) (Category.assoc τ μ (ρ ≫ σ))).trans
          ((congrArg (fun z => ε ≫ τ ≫ z) hm).trans
            ((congrArg (fun z => ε ≫ z) ht).trans
              (he.trans (diagramEtaleTest_cocone_snd X i T c a).symm)))))

/-- The test-cocone arrow retains the original site triangle under its chart isomorphisms. -/
lemma diagramEtaleTestConeArrow_chartIso (a : Under i) :
    (diagramEtaleTestLimitChartIso X i T c).inv ≫ diagramEtaleTestConeArrow X i T c a =
      (siteBaseChangeTriangleIso (X.map a.hom).unop (c.ι.app i).unop
        (c.ι.app a.right).unop (coneSquare X c a.hom)).hom.app T ≫
        (siteBaseChange (c.ι.app a.right).unop).map (diagramEtaleTestChartIso X i T a).inv := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫
      ((siteBaseChangeTriangleIso (X.map a.hom).unop (c.ι.app i).unop
        (c.ι.app a.right).unop (coneSquare X c a.hom)).hom.app T ≫
        (siteBaseChange (c.ι.app a.right).unop).map
          (diagramEtaleTestChartIso X i T a).inv))
      (diagramEtaleTestLimitChartIso X i T c).inv_hom_id).trans (Category.id_comp _))

variable [HasColimit (coneCoefficientFunctor X c F)]

/-- The actual apex comparison only changes the native limit test chart. -/
def diagramTestRightTailPointIso :
    (colimit (coneCoefficientFunctor X c F)).obj.obj
        (op (diagramEtaleTestLimitChart X i T c)) ≅
      ((diagramRightTailCocone X F c i).pt).obj.obj (op T) :=
  (colimit (coneCoefficientFunctor X c F)).obj.mapIso
    (diagramEtaleTestLimitChartIso X i T c).symm.op

/-- An original right-tail cocone leg is its adjoint component and site triangle. -/
lemma diagramRightTailLeg_component (a : Under i) :
    (diagramRightTailLeg X F c a.hom).hom.app (op T) =
      (diagramAdjointLeg X c F a.right).hom.app
        (op ((siteBaseChange (X.map a.hom).unop).obj T)) ≫
      (colimit (coneCoefficientFunctor X c F)).obj.map
        ((siteBaseChangeTriangleIso (X.map a.hom).unop (c.ι.app i).unop
          (c.ι.app a.right).unop (coneSquare X c a.hom)).hom.app T).op :=
  congrArg
    (fun z => (diagramAdjointLeg X c F a.right).hom.app
      (op ((siteBaseChange (X.map a.hom).unop).obj T)) ≫ z)
    (directImageTriangleIso_component (X.map a.hom).unop (c.ι.app i).unop
      (c.ι.app a.right).unop (coneSquare X c a.hom)
      (colimit (coneCoefficientFunctor X c F)) T)

/-- The original coefficient insertion transferred along the actual test-cone square. -/
def diagramTestSquareRightTailLeg (a : Under i) :
    (globalSections (diagramEtaleTestChart X i T a).left).obj
        ((inverseImage (diagramEtaleTestChart X i T a).hom).obj (F.obj a.right)) ⟶
      (globalSections (diagramEtaleTestLimitChart X i T c).left).obj
        ((inverseImage (diagramEtaleTestLimitChart X i T c).hom).obj
          (colimit (coneCoefficientFunctor X c F))) :=
  squareSectionsMap (diagramEtaleTestChart X i T a).hom
    (diagramEtaleTestLimitChart X i T c).hom (c.ι.app a.right).unop
    ((diagramEtaleTestCocone X i T c).ι.app a).unop
    (diagramEtaleTest_cocone_fst X i T c a).symm
    (colimit.ι (coneCoefficientFunctor X c F) a.right)

/-- The actual square leg becomes the original evaluated right-tail leg. -/
lemma diagramTestSquareRightTailLeg_evaluation (a : Under i) :
    diagramTestSquareRightTailLeg X F i T c a ≫
        (pullbackSectionsEtaleEvaluationIso (colimit (coneCoefficientFunctor X c F))
          (diagramEtaleTestLimitChart X i T c)).hom ≫
        (diagramTestRightTailPointIso X F i T c).hom =
      (diagramTestChartSectionsIso X F i T a).hom ≫
        (diagramRightTailLeg X F c a.hom).hom.app (op T) := by
  have h := squareSectionsMap_chartIso_coefficient (c.ι.app a.right).unop
    (colimit.ι (coneCoefficientFunctor X c F) a.right)
    (diagramEtaleTestChartIso X i T a) (diagramEtaleTestLimitChartIso X i T c)
    ((siteBaseChangeTriangleIso (X.map a.hom).unop (c.ι.app i).unop
      (c.ι.app a.right).unop (coneSquare X c a.hom)).hom.app T)
    (diagramEtaleTestConeArrow X i T c a) (diagramEtaleTestConeArrow_chartIso X i T c a)
    ((diagramEtaleTestCocone X i T c).ι.app a).unop
    (diagramEtaleTestConeArrow_left X i T c a).symm
    (diagramEtaleTest_cocone_fst X i T c a).symm
  exact h.trans (congrArg (fun q => (diagramTestChartSectionsIso X F i T a).hom ≫ q)
    (diagramRightTailLeg_component X F i T c a).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
