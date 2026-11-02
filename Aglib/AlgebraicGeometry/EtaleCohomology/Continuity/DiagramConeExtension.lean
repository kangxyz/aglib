/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestBaseSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeSquares
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleSections
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeExtension

/-! # The original coefficient diagram under extension of the same scheme cocone -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (c : Cocone X) (F : DiagramCoefficientSystem X)

/-- The whole extension law retains the original inverse-image and triangle comparisons. -/
lemma coneCoefficientExtendTriangle_whole {V : Scheme.{u}} (l : V ⟶ c.pt.unop)
    {j k : I} (a : j ⟶ k) :
    (pullbackTriangleIso ((c.extend l.op).ι.app j).unop (X.map a).unop
      ((c.extend l.op).ι.app k).unop (coneSquare X (c.extend l.op) a)).hom ≫
        Functor.whiskerLeft (inverseImage (X.map a).unop)
          (inverseImageComp (c.ι.app k).unop l).hom =
      (inverseImageComp (c.ι.app j).unop l).hom ≫
        Functor.whiskerRight
          (pullbackTriangleIso (c.ι.app j).unop (X.map a).unop
            (c.ι.app k).unop (coneSquare X c a)).hom (inverseImage l) ≫
          (Functor.associator (inverseImage (X.map a).unop)
            (inverseImage (c.ι.app k).unop) (inverseImage l)).hom := by
  exact InjectiveSystem.AdjunctionData.triangleIso_postcompose_whole_of_eq
    schemeAdjunctionData schemeAdjunctionData_coherent
    (X.map a) (c.ι.app j) (c.ι.app k) (c.w a) l.op
    (inverseImageComp (c.ι.app j).unop l) (inverseImageComp (c.ι.app k).unop l)
    (pullbackTriangleIso (c.ι.app j).unop (X.map a).unop
      (c.ι.app k).unop (coneSquare X c a))
    (pullbackTriangleIso ((c.extend l.op).ι.app j).unop (X.map a).unop
      ((c.extend l.op).ι.app k).unop (coneSquare X (c.extend l.op) a))
    (schemeLeftCompIso_eq_inverseImageComp (c.ι.app j) l.op).symm
    (schemeLeftCompIso_eq_inverseImageComp (c.ι.app k) l.op).symm
    (schemeTriangleIso_eq_pullbackTriangleIso (X.map a) (c.ι.app j) (c.ι.app k) (c.w a)).symm
    (schemeTriangleIso_eq_pullbackTriangleIso (X.map a)
      ((c.extend l.op).ι.app j) ((c.extend l.op).ι.app k) ((c.extend l.op).w a)).symm

/-- Extend the same cone coefficient diagram using the original composition isomorphisms. -/
def coneCoefficientExtendIso {V : Scheme.{u}} (l : V ⟶ c.pt.unop) :
    coneCoefficientFunctor X (c.extend l.op) F ≅
      coneCoefficientFunctor X c F ⋙ inverseImage l :=
  InjectiveSystem.AdjunctionData.Cone.coefficientExtendIso
    (diagramConeAdjunctionData X c) (diagramConeAdjunctionData X (c.extend l.op))
    (inverseImage l) (fun j => inverseImageComp (c.ι.app j).unop l)
    (fun a => coneCoefficientExtendTriangle_whole X c l a) F

/-- The actual extension component is the original inverse-image composition component. -/
lemma coneCoefficientExtendIso_hom_app {V : Scheme.{u}} (l : V ⟶ c.pt.unop) (j : I) :
    (coneCoefficientExtendIso X c F l).hom.app j =
      (inverseImageComp (c.ι.app j).unop l).hom.app (F.obj j) :=
  InjectiveSystem.AdjunctionData.Cone.coefficientExtendIso_hom_app
    (diagramConeAdjunctionData X c) (diagramConeAdjunctionData X (c.extend l.op))
    (inverseImage l) (fun j => inverseImageComp (c.ι.app j).unop l)
    (fun a => coneCoefficientExtendTriangle_whole X c l a) F j

/-- Whole section diagrams on an étale extension, before selecting a source stage. -/
def coneCoefficientEtaleSectionsIso (U : c.pt.unop.Etale) :
    coneCoefficientFunctor X (c.extend U.hom.op) F ⋙
        globalSections (c.extend U.hom.op).pt.unop ≅
      coneCoefficientFunctor X c F ⋙
        (sheafSections c.pt.unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U) :=
  InjectiveSystem.AdjunctionData.Cone.coefficientExtendSectionsIso
    (diagramConeAdjunctionData X c) (diagramConeAdjunctionData X (c.extend U.hom.op))
    (inverseImage U.hom) (fun j => inverseImageComp (c.ι.app j).unop U.hom)
    (fun a => coneCoefficientExtendTriangle_whole X c U.hom a) F
    (globalSections U.left)
    ((sheafSections c.pt.unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U))
    (pullbackSectionsEtaleEvaluationNatIso U)

/-- The whole diagram comparison retains the original relative-base component. -/
lemma coneCoefficientEtaleSectionsIso_hom_app (U : c.pt.unop.Etale) (j : I) :
    (coneCoefficientEtaleSectionsIso X c F U).hom.app j =
      (pullbackSectionsBaseEtaleIso (c.ι.app j).unop (F.obj j)).hom.app (op U) :=
  InjectiveSystem.AdjunctionData.Cone.coefficientExtendSectionsIso_hom_app_eq
    (diagramConeAdjunctionData X c) (diagramConeAdjunctionData X (c.extend U.hom.op))
    (inverseImage U.hom) (fun j => inverseImageComp (c.ι.app j).unop U.hom)
    (fun a => coneCoefficientExtendTriangle_whole X c U.hom a) F
    (globalSections U.left)
    ((sheafSections c.pt.unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U))
    (pullbackSectionsEtaleEvaluationNatIso U) j
    ((pullbackSectionsBaseEtaleIso (c.ι.app j).unop (F.obj j)).hom.app (op U))
    (pullbackSectionsBaseEtaleIso_hom_app (c.ι.app j).unop (F.obj j) U).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
