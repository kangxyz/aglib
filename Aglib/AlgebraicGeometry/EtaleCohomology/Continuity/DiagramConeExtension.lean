/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestBaseSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeSquares
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleSections

/-! # The original coefficient diagram under extension of the same scheme cocone -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (c : Cocone X) (F : DiagramCoefficientSystem X)

/-- Extend the same cone coefficient diagram using the original composition isomorphisms. -/
def coneCoefficientExtendIso {V : Scheme.{u}} (l : V ⟶ c.pt.unop) :
    coneCoefficientFunctor X (c.extend l.op) F ≅
      coneCoefficientFunctor X c F ⋙ inverseImage l :=
  NatIso.ofComponents (fun j => (inverseImageComp (c.ι.app j).unop l).app (F.obj j))
    (fun {j k} a => triangleCoefficientMap_postcompose (X.map a).unop
      (c.ι.app j).unop (c.ι.app k).unop (coneSquare X c a) l
      (diagramInverseTransition X F a))

/-- Whole section diagrams on an étale extension, before selecting a source stage. -/
def coneCoefficientEtaleSectionsIso (U : c.pt.unop.Etale) :
    coneCoefficientFunctor X (c.extend U.hom.op) F ⋙
        globalSections (c.extend U.hom.op).pt.unop ≅
      coneCoefficientFunctor X c F ⋙
        (sheafSections c.pt.unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U) :=
  Functor.isoWhiskerRight (coneCoefficientExtendIso X c F U.hom)
      (globalSections (c.extend U.hom.op).pt.unop) ≪≫
    Functor.associator (coneCoefficientFunctor X c F) (inverseImage U.hom)
      (globalSections (c.extend U.hom.op).pt.unop) ≪≫
    Functor.isoWhiskerLeft (coneCoefficientFunctor X c F)
      (pullbackSectionsEtaleEvaluationNatIso U)

/-- The whole diagram comparison retains the original relative-base component. -/
lemma coneCoefficientEtaleSectionsIso_hom_app (U : c.pt.unop.Etale) (j : I) :
    (coneCoefficientEtaleSectionsIso X c F U).hom.app j =
      (pullbackSectionsBaseEtaleIso (c.ι.app j).unop (F.obj j)).hom.app (op U) := by
  change (globalSections U.left).map ((inverseImageComp (c.ι.app j).unop U.hom).hom.app
    (F.obj j)) ≫ (𝟙 _ ≫
      (pullbackSectionsEtaleEvaluationIso
        ((inverseImage (c.ι.app j).unop).obj (F.obj j)) U).hom) = _
  rw [Category.id_comp]
  exact (pullbackSectionsBaseEtaleIso_hom_app (c.ι.app j).unop (F.obj j) U).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
