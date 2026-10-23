/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestRightTailComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestRightTailLeg
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestConeSections

/-! # Canonical original legs of the evaluated right-tail comparison

The direct double-tail section maps retain the actual coefficient insertions.
Their apex comparison is evaluation along the native limit-chart symmetry,
not an identification of a new pulled-system coefficient colimit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

/-- Normalize only the structural arrow in an original relative section map. -/
lemma pullbackSectionsMap_source_transport {X Y Z : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (u u' : Y ⟶ X) (w : Z ⟶ X)
    (e : u = u') (r : Z ⟶ Y) (h : r ≫ u = w) (h' : r ≫ u' = w) :
    pullbackSectionsMap F (Over.homMk r h : Over.mk w ⟶ Over.mk u) =
      (globalSections Y).map (eqToHom (congrArg (fun f => (inverseImage f).obj F) e)) ≫
        pullbackSectionsMap F (Over.homMk r h' : Over.mk w ⟶ Over.mk u') := by
  subst u'
  simp only [eqToHom_refl]
  exact (Category.id_comp _).symm.trans
    (congrArg (fun q => q ≫
      pullbackSectionsMap F (Over.homMk r h' : Over.mk w ⟶ Over.mk u))
      ((globalSections Y).map_id ((inverseImage u).obj F)).symm)

/-- The relative-section square remains an equality before evaluating any coefficient. -/
lemma pullbackSectionsBifunctor_comp_square_evaluation {X S : Scheme.{u}}
    (p : S ⟶ X) (U : X.Etale) (W : S.Etale)
    (a : Over.mk (W.hom ≫ p) ⟶ Over.mk U.hom) :
    (pullbackSectionsBifunctor X).map a.op ≫
        Functor.whiskerRight (inverseImageComp p W.hom).hom (globalSections W.left) ≫
        Functor.whiskerLeft (inverseImage p) (pullbackSectionsEtaleEvaluationNatIso W).hom =
      squareSectionsNatTrans U.hom W.hom p a.left (Over.w a).symm ≫
        Functor.whiskerLeft (inverseImage p) (pullbackSectionsEtaleEvaluationNatIso W).hom :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ Functor.whiskerLeft (inverseImage p)
      (pullbackSectionsEtaleEvaluationNatIso W).hom)
      (pullbackSectionsBifunctor_comp_square p U.hom W.hom a))

/-- Evaluate the original whole square and identify its original base-comparison component. -/
lemma pullbackSectionsMap_baseEtale {X S : Scheme.{u}} (p : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (U : X.Etale) (W : S.Etale)
    (a : Over.mk (W.hom ≫ p) ⟶ Over.mk U.hom) :
    pullbackSectionsMap F a ≫ (pullbackSectionsBaseEtaleIso p F).hom.app (op W) =
      (squareSectionsNatTrans U.hom W.hom p a.left (Over.w a).symm).app F ≫
        (pullbackSectionsEtaleEvaluationIso ((inverseImage p).obj F) W).hom := by
  have hm := pullbackSectionsBifunctor_map_app a F
  have hb := pullbackSectionsBaseEtaleIso_hom_app p F W
  have hw := NatTrans.congr_app (pullbackSectionsBifunctor_comp_square_evaluation p U W a) F
  exact (congrArg₂ (fun q r => q ≫ r) hm.symm hb).trans hw

/-- Paste the two actual section squares at their common native morphism boundary. -/
lemma sectionSquare_postcompose {C : Type*} [Category* C] {A B D E H K : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ K) (d : A ⟶ E)
    (e : E ⟶ D) (f : E ⟶ H) (g : H ⟶ K) (h : A ⟶ H)
    (hab : a ≫ b = d ≫ e) (hec : e ≫ c = f ≫ g) (hdf : d ≫ f = h) :
    a ≫ b ≫ c = h ≫ g := by
  rw [← Category.assoc, hab, Category.assoc, hec, ← Category.assoc, hdf]

/-- Relative sections, original base comparison and a coefficient map form the original square. -/
lemma pullbackSectionsMap_baseEtale_coefficient {X S : Scheme.{u}}
    (p : S ⟶ X) {F : AbelianSheaf.{u, u + 1} X}
    {G : AbelianSheaf.{u, u + 1} S} (φ : (inverseImage p).obj F ⟶ G)
    (U : X.Etale) (W : S.Etale)
    (a : Over.mk (W.hom ≫ p) ⟶ Over.mk U.hom) :
    pullbackSectionsMap F a ≫ (pullbackSectionsBaseEtaleIso p F).hom.app (op W) ≫
        φ.hom.app (op W) =
      squareSectionsMap U.hom W.hom p a.left (Over.w a).symm φ ≫
        (pullbackSectionsEtaleEvaluationIso G W).hom :=
  sectionSquare_postcompose _ _ _ _ _ _ _ _
    (pullbackSectionsMap_baseEtale p F U W a)
    (pullbackSectionsEtaleEvaluationIso_naturality φ W).symm
    (squareSectionsMap_natTrans U.hom W.hom p a.left (Over.w a).symm φ).symm

/-- Reassociate the original five native leg factors before geometric specialization. -/
lemma sectionLeg_assoc {C : Type*} [Category* C] {A B D E H K : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ H) (e : H ⟶ K) :
    (a ≫ b) ≫ c ≫ d ≫ e = a ≫ (b ≫ c ≫ d) ≫ e := by
  simp only [Category.assoc]

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (c : Cocone X) (i : I)
  (T : (X.obj i).unop.Etale)

/-- Normalize the source of the actual diagonal relative cone map. -/
lemma diagramTestConeArrowOverHom_diagonal_sections (a : Under i) :
    pullbackSectionsMap (F.obj a.right)
        (diagramTestConeArrowOverHom X c i T (Arrow.mk (𝟙 a))) =
      (diagramTestDiagonalNormalizeIso X F i T a).hom ≫
        pullbackSectionsMap (F.obj a.right)
          (Over.homMk ((diagramEtaleTestCocone X i T c).ι.app a).unop
            (diagramEtaleTest_cocone_fst X i T c a) :
            Over.mk ((diagramEtaleTestLimitChart X i T c).hom ≫ (c.ι.app a.right).unop) ⟶
              Over.mk (diagramEtaleTestChart X i T a).hom) :=
  pullbackSectionsMap_source_transport (F.obj a.right)
    (diagramTestArrowSchemeMap X i T (Arrow.mk (𝟙 a)))
    (diagramEtaleTestChart X i T a).hom
    ((diagramEtaleTestLimitChart X i T c).hom ≫ (c.ι.app a.right).unop)
    (diagramTestArrowSchemeMap_diagonal X i T a)
    ((diagramEtaleTestCocone X i T c).ι.app a).unop
    (diagramTestConeArrowTriangle X c i T (Arrow.mk (𝟙 a)))
    (diagramEtaleTest_cocone_fst X i T c a)

variable [HasColimit (coneCoefficientFunctor X c F)]

/-- The literal relative-map leg retains the original right-tail insertion under the point map. -/
lemma diagramTestDiagonalLeg_rightTail (a : Under i) :
    pullbackSectionsMap (F.obj a.right)
        (diagramTestConeArrowOverHom X c i T (Arrow.mk (𝟙 a))) ≫
        (pullbackSectionsBaseEtaleIso (c.ι.app a.right).unop (F.obj a.right)).hom.app
          (op (diagramEtaleTestLimitChart X i T c)) ≫
        (colimit.ι (coneCoefficientFunctor X c F) a.right).hom.app
          (op (diagramEtaleTestLimitChart X i T c)) ≫
        (diagramTestRightTailPointIso X F i T c).hom =
      (diagramTestDiagonalRightTailComponent X F i T a).hom ≫
        (diagramRightTailLeg X F c a.hom).hom.app (op T) := by
  let ρ : Over.mk ((diagramEtaleTestLimitChart X i T c).hom ≫ (c.ι.app a.right).unop) ⟶
      Over.mk (diagramEtaleTestChart X i T a).hom :=
    Over.homMk ((diagramEtaleTestCocone X i T c).ι.app a).unop
      (diagramEtaleTest_cocone_fst X i T c a)
  have h₀ := diagramTestConeArrowOverHom_diagonal_sections X F c i T a
  have h₁ := pullbackSectionsMap_baseEtale_coefficient (c.ι.app a.right).unop
    (colimit.ι (coneCoefficientFunctor X c F) a.right)
    (diagramEtaleTestChart X i T a) (diagramEtaleTestLimitChart X i T c) ρ
  have h₂ := diagramTestSquareRightTailLeg_evaluation X F i T c a
  calc
    _ = ((diagramTestDiagonalNormalizeIso X F i T a).hom ≫
        pullbackSectionsMap (F.obj a.right) ρ) ≫
        (pullbackSectionsBaseEtaleIso (c.ι.app a.right).unop (F.obj a.right)).hom.app
          (op (diagramEtaleTestLimitChart X i T c)) ≫
        (colimit.ι (coneCoefficientFunctor X c F) a.right).hom.app
          (op (diagramEtaleTestLimitChart X i T c)) ≫
        (diagramTestRightTailPointIso X F i T c).hom :=
      congrArg (fun q => q ≫
        (pullbackSectionsBaseEtaleIso (c.ι.app a.right).unop (F.obj a.right)).hom.app
          (op (diagramEtaleTestLimitChart X i T c)) ≫
        (colimit.ι (coneCoefficientFunctor X c F) a.right).hom.app
          (op (diagramEtaleTestLimitChart X i T c)) ≫
        (diagramTestRightTailPointIso X F i T c).hom) h₀
    _ = (diagramTestDiagonalNormalizeIso X F i T a).hom ≫
        (pullbackSectionsMap (F.obj a.right) ρ ≫
        (pullbackSectionsBaseEtaleIso (c.ι.app a.right).unop (F.obj a.right)).hom.app
          (op (diagramEtaleTestLimitChart X i T c)) ≫
        (colimit.ι (coneCoefficientFunctor X c F) a.right).hom.app
          (op (diagramEtaleTestLimitChart X i T c))) ≫
        (diagramTestRightTailPointIso X F i T c).hom := sectionLeg_assoc _ _ _ _ _
    _ = (diagramTestDiagonalNormalizeIso X F i T a).hom ≫
        (diagramTestSquareRightTailLeg X F i T c a ≫
        (pullbackSectionsEtaleEvaluationIso (colimit (coneCoefficientFunctor X c F))
          (diagramEtaleTestLimitChart X i T c)).hom) ≫
        (diagramTestRightTailPointIso X F i T c).hom :=
      congrArg (fun q => (diagramTestDiagonalNormalizeIso X F i T a).hom ≫ q ≫
        (diagramTestRightTailPointIso X F i T c).hom) h₁
    _ = _ := (congrArg (fun q => (diagramTestDiagonalNormalizeIso X F i T a).hom ≫ q)
      ((Category.assoc _ _ _).trans h₂)).trans (Category.assoc _ _ _).symm

/-- The actual diagonal cocone built from the relative rows and original coefficient insertions. -/
def diagramTestDiagonalCocone :
    Cocone (SchemeSystemColimits.diagonal ⋙ diagramTestArrowSectionsFunctor X F i T) :=
  (SchemeSystemColimits.outerCocone (diagramTestArrowSectionsFunctor X F i T)
    (diagramTestConeSectionsFunctor X F c i T) (diagramTestConeSectionsNatTrans X F c i T)
    (diagramTestConeSectionsCocone X F c i T)).whisker SchemeSystemColimits.diagonal

/-- The double-tail diagonal cocone is the evaluated original right-tail cocone. -/
def diagramTestDiagonalRightTailCoconeIso :
    diagramTestDiagonalCocone X F c i T ≅
      (Cocone.precompose (diagramTestDiagonalRightTailIso X F i T).hom).obj
        (((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op T)).mapCocone (diagramRightTailCocone X F c i)) := by
  refine Cocone.ext (diagramTestRightTailPointIso X F i T c) (fun a => ?_)
  change ((diagramTestConeSectionsNatTrans X F c i T).app (Arrow.mk (𝟙 a)) ≫
      (colimit.ι (coneCoefficientFunctor X c F) a.right).hom.app
        (op (diagramEtaleTestLimitChart X i T c))) ≫
      (diagramTestRightTailPointIso X F i T c).hom =
    (diagramTestDiagonalRightTailComponent X F i T a).hom ≫
      (diagramRightTailLeg X F c a.hom).hom.app (op T)
  have h := congrArg (fun q => (q ≫
    (colimit.ι (coneCoefficientFunctor X c F) a.right).hom.app
      (op (diagramEtaleTestLimitChart X i T c))) ≫
    (diagramTestRightTailPointIso X F i T c).hom)
    (diagramTestConeSectionsNatTrans_app X F c i T (Arrow.mk (𝟙 a)))
  exact h.trans ((Category.assoc _ _ _).trans
    ((Category.assoc _ _ _).trans (diagramTestDiagonalLeg_rightTail X F c i T a)))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
