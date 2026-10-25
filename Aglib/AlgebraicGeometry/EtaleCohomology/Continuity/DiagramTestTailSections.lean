/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestRelativeTail
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestConeSections
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.CoconeDoubleOpposite

/-! # Transport of original fixed-coefficient test rows to the canonical Arrow tails -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (c : Cocone X) (i : I)
  (T : (X.obj i).unop.Etale) (a : Under i)

lemma diagramTestTailSectionsMap_eq {b d : Under a} (m : b ⟶ d) :
    (SchemeSystemColimits.tailToArrow a ⋙ diagramTestArrowSectionsFunctor X F i T).map m =
      (diagramTestRelativeTail X i T a ⋙ pullbackSectionsFunctor (F.obj a.right)).map m := by
  change squareSectionsMap (diagramTestArrowSchemeMap X i T (Arrow.mk b.hom))
    (diagramTestArrowSchemeMap X i T (Arrow.mk d.hom)) (X.map (𝟙 a.right)).unop
    ((diagramEtaleTest X i T).map m.right).unop _
    (diagramInverseTransition X F (𝟙 a.right)) =
      pullbackSectionsMap (F.obj a.right) ((diagramTestRelativeTail X i T a).map m).unop
  rw [diagramInverseTransition_id]
  simp only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  let q := ((diagramTestRelativeTail X i T a).map m).unop
  have ht := squareSectionsMap_transport
    (diagramTestArrowSchemeMap X i T (Arrow.mk b.hom))
    (diagramTestArrowSchemeMap X i T (Arrow.mk d.hom))
    (𝟙 _) (X.map (𝟙 a.right)).unop
    ((diagramEtaleTest X i T).map m.right).unop
    ((diagramEtaleTest X i T).map m.right).unop
    (congrArg Quiver.Hom.unop (X.map_id a.right)) rfl
    ((Category.comp_id _).trans q.w.symm)
    (diagramTestArrowSquare X i T ((SchemeSystemColimits.tailToArrow a).map m))
    ((inverseImageId (X.obj a.right).unop).hom.app (F.obj a.right))
  exact ht.trans (squareSectionsMap_base_id (F.obj a.right) q)

/-- The row restriction is the original fixed-coefficient relative section diagram. -/
def diagramTestTailSectionsIso :
    SchemeSystemColimits.tailToArrow a ⋙ diagramTestArrowSectionsFunctor X F i T ≅
      diagramTestRelativeTail X i T a ⋙ pullbackSectionsFunctor (F.obj a.right) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_b _d} m =>
    (Category.comp_id _).trans ((diagramTestTailSectionsMap_eq X F i T a m).trans
      (Category.id_comp _).symm))

/-- Original relative section cocone on a fixed-source test row. -/
def diagramTestRelativeTailSectionsCocone :
    Cocone (diagramTestRelativeTail X i T a ⋙ pullbackSectionsFunctor (F.obj a.right)) :=
  (pullbackSectionsFunctor (F.obj a.right)).mapCocone
    (diagramTestRelativeTailCocone X c i T a)

/-- The canonical row cocone of the actual test Arrow comparison. -/
def diagramTestTailSectionsCocone :
    Cocone (SchemeSystemColimits.tailToArrow a ⋙ diagramTestArrowSectionsFunctor X F i T) :=
  SchemeSystemColimits.tailCocone (diagramTestArrowSectionsFunctor X F i T)
    (diagramTestConeSectionsFunctor X F c i T) (diagramTestConeSectionsNatTrans X F c i T) a

/-- The original relative cocone is identified with the canonical row, including its apex. -/
def diagramTestRelativeTailSectionsCoconeIso :
    (Cocone.precompose (diagramTestTailSectionsIso X F i T a).hom).obj
      (diagramTestRelativeTailSectionsCocone X F c i T a) ≅
        diagramTestTailSectionsCocone X F c i T a := by
  refine Cocone.ext (diagramTestConeSectionsIso X F c i T a) (fun b => ?_)
  change (𝟙 _ ≫ pullbackSectionsMap (F.obj a.right)
      (diagramTestConeArrowOverHom X c i T (Arrow.mk b.hom))) ≫
        (diagramTestConeSectionsIso X F c i T a).hom =
      diagramTestConeArrowSectionsMap X F c i T (Arrow.mk b.hom) ≫
        (diagramTestConeSectionsIso X F c i T a).hom
  rw [Category.id_comp, diagramTestConeArrowSectionsMap_eq_pullback]
  rfl

/-- Remove only the double-opposite index from the original geometric row certificate. -/
def isColimitDiagramTestRelativeTailOfNative
    (h : IsColimit (pullbackSectionsCocone (diagramTestRelativeTail X i T a).leftOp
      (diagramTestRelativeTailCone X c i T a) (F.obj a.right))) :
    IsColimit (diagramTestRelativeTailSectionsCocone X F c i T a) :=
  isColimitMapCoconeOfLeftOp (diagramTestRelativeTail X i T a)
    (diagramTestRelativeTailCocone X c i T a) (pullbackSectionsFunctor (F.obj a.right)) h

/-- Transport the native geometric row certificate, without assuming evaluated continuity. -/
def isColimitDiagramTestTailOfNative
    (h : IsColimit (pullbackSectionsCocone (diagramTestRelativeTail X i T a).leftOp
      (diagramTestRelativeTailCone X c i T a) (F.obj a.right))) :
    IsColimit (diagramTestTailSectionsCocone X F c i T a) := by
  have hr := isColimitDiagramTestRelativeTailOfNative X F c i T a h
  exact IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (diagramTestTailSectionsIso X F i T a) _).symm hr)
    (diagramTestRelativeTailSectionsCoconeIso X F c i T a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
