/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestArrowSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestChartComparisons

/-! # The actual diagonal of test sections and the original right tail

Only the original identity-arrow transport, chart evaluation and pullback
symmetry identify the diagonal. The comparison retains the original square
section maps and right-adjoint transition triangles. No pulled-system
coefficient-colimit comparison or section-continuity premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u uI vI

attribute [local instance] hasSheafifyLarge

/-- Equality transport of the two structural arrows preserves the original square transfer. -/
lemma squareSectionsMap_structural_transport {X₀ S₀ X₁ S₁ : Scheme.{u}}
    (f₀ f₀' : X₀ ⟶ S₀) (f₁ f₁' : X₁ ⟶ S₁) (e₀ : f₀ = f₀') (e₁ : f₁ = f₁')
    (g : S₁ ⟶ S₀) (h : X₁ ⟶ X₀)
    (e : f₁ ≫ g = h ≫ f₀) (e' : f₁' ≫ g = h ≫ f₀')
    {F : AbelianSheaf.{u, u + 1} S₀} {G : AbelianSheaf.{u, u + 1} S₁}
    (φ : (inverseImage g).obj F ⟶ G) :
    squareSectionsMap f₀ f₁ g h e φ ≫
        (globalSections X₁).map
          (eqToHom (congrArg (fun f => (inverseImage f).obj G) e₁)) =
      (globalSections X₀).map
          (eqToHom (congrArg (fun f => (inverseImage f).obj F) e₀)) ≫
        squareSectionsMap f₀' f₁' g h e' φ := by
  subst f₀'
  subst f₁'
  simp only [eqToHom_refl]
  have h₀ := (globalSections X₀).map_id ((inverseImage f₀).obj F)
  have h₁ := (globalSections X₁).map_id ((inverseImage f₁).obj G)
  exact (congrArg (fun q => squareSectionsMap f₀ f₁ g h e φ ≫ q) h₁).trans
    ((Category.comp_id _).trans ((Category.id_comp _).symm.trans
      (congrArg (fun q => q ≫ squareSectionsMap f₀ f₁ g h e' φ) h₀.symm)))

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (i : I) (T : (X.obj i).unop.Etale)

/-- Remove only the original identity-arrow transport on the direct diagonal. -/
def diagramTestDiagonalNormalizeIso (a : Under i) :
    diagramTestArrowSectionsObj X F i T (Arrow.mk (𝟙 a)) ≅
      (globalSections (diagramEtaleTestChart X i T a).left).obj
        ((inverseImage (diagramEtaleTestChart X i T a).hom).obj (F.obj a.right)) :=
  (globalSections (diagramEtaleTestChart X i T a).left).mapIso
    (eqToIso (congrArg (fun f => (inverseImage f).obj (F.obj a.right))
      (diagramTestArrowSchemeMap_diagonal X i T a)))

/-- The original square map commutes with the diagonal structural-arrow normalization. -/
lemma diagramTestDiagonalNormalizeIso_naturality {a b : Under i} (m : a ⟶ b) :
    diagramTestArrowSectionsMap X F i T (SchemeSystemColimits.diagonal.map m) ≫
        (diagramTestDiagonalNormalizeIso X F i T b).hom =
      (diagramTestDiagonalNormalizeIso X F i T a).hom ≫
        squareSectionsMap (diagramEtaleTestChart X i T a).hom
          (diagramEtaleTestChart X i T b).hom (X.map m.right).unop
          ((diagramEtaleTest X i T).map m).unop (diagramEtaleTest_map_fst X i T m).symm
          (diagramInverseTransition X F m.right) :=
  squareSectionsMap_structural_transport
    (diagramTestArrowSchemeMap X i T (Arrow.mk (𝟙 a))) (diagramEtaleTestChart X i T a).hom
    (diagramTestArrowSchemeMap X i T (Arrow.mk (𝟙 b))) (diagramEtaleTestChart X i T b).hom
    (diagramTestArrowSchemeMap_diagonal X i T a) (diagramTestArrowSchemeMap_diagonal X i T b)
    (X.map m.right).unop ((diagramEtaleTest X i T).map m).unop
    (diagramTestArrowSquare X i T (SchemeSystemColimits.diagonal.map m))
    (diagramEtaleTest_map_fst X i T m).symm (diagramInverseTransition X F m.right)

/-- Direct original chart sections commute with the actual right-tail transition. -/
lemma diagramTestChartSectionsIso_naturality {a b : Under i} (m : a ⟶ b) :
    squareSectionsMap (diagramEtaleTestChart X i T a).hom
        (diagramEtaleTestChart X i T b).hom (X.map m.right).unop
        ((diagramEtaleTest X i T).map m).unop (diagramEtaleTest_map_fst X i T m).symm
        (diagramInverseTransition X F m.right) ≫ (diagramTestChartSectionsIso X F i T b).hom =
      (diagramTestChartSectionsIso X F i T a).hom ≫
        ((diagramRightTail X F i).map m).hom.app (op T) := by
  have h := squareSectionsMap_chartIso (X.map m.right).unop (F.map m.right)
    (diagramEtaleTestChartIso X i T a) (diagramEtaleTestChartIso X i T b)
    ((siteBaseChangeTriangleIso (X.map a.hom).unop (X.map b.hom).unop
      (X.map m.right).unop (diagramEtaleTest_triangle X i m)).hom.app T)
    (diagramEtaleTestArrow X i T m) (diagramEtaleTestArrow_chartIso X i T m)
    ((diagramEtaleTest X i T).map m).unop (diagramEtaleTestArrow_left X i T m).symm
    (diagramEtaleTest_map_fst X i T m).symm
  exact h.trans (congrArg (fun z => (diagramTestChartSectionsIso X F i T a).hom ≫ z)
    (diagramRightTail_map_component X F i T m).symm)

/-- The original diagonal comparison at one stage. -/
def diagramTestDiagonalRightTailComponent (a : Under i) :
    diagramTestArrowSectionsObj X F i T (Arrow.mk (𝟙 a)) ≅
      ((diagramRightTail X F i).obj a).obj.obj (op T) :=
  diagramTestDiagonalNormalizeIso X F i T a ≪≫ diagramTestChartSectionsIso X F i T a

/-- Both original map comparisons paste without introducing another coefficient system. -/
lemma diagramTestDiagonalRightTailComponent_naturality {a b : Under i} (m : a ⟶ b) :
    diagramTestArrowSectionsMap X F i T (SchemeSystemColimits.diagonal.map m) ≫
        (diagramTestDiagonalRightTailComponent X F i T b).hom =
      (diagramTestDiagonalRightTailComponent X F i T a).hom ≫
        ((diagramRightTail X F i).map m).hom.app (op T) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (diagramTestChartSectionsIso X F i T b).hom)
      (diagramTestDiagonalNormalizeIso_naturality X F i T m)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => (diagramTestDiagonalNormalizeIso X F i T a).hom ≫ z)
          (diagramTestChartSectionsIso_naturality X F i T m)).trans
            (Category.assoc _ _ _).symm)))

/-- The actual test-arrow diagonal is the original evaluated right-tail diagram. -/
def diagramTestDiagonalRightTailIso :
    SchemeSystemColimits.diagonal ⋙ diagramTestArrowSectionsFunctor X F i T ≅
      diagramRightTail X F i ⋙
        (sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op T) :=
  NatIso.ofComponents (diagramTestDiagonalRightTailComponent X F i T)
    (fun m => diagramTestDiagonalRightTailComponent_naturality X F i T m)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
