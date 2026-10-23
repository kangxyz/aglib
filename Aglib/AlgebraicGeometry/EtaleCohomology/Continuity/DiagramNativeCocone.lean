/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramDiagonalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTailCocones

/-! # The original compatible-system degree-zero comparison cocone

The final transport consumes genuine native fixed-coefficient tail certificates;
it does not prove their existence or scheme-limit continuity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge
variable {I : Type u} [Category.{u} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (c : Cocone X)

lemma diagonalConeArrowSectionsMap (i : I) :
    (globalSections (X.obj i).unop).map ((diagramInverseImageId X i).hom.app (F.obj i)) ≫
      globalSectionsPullback (c.ι.app i).unop (F.obj i) =
        coneArrowSectionsMap X F c (Arrow.mk (𝟙 i)) := by
  let e := (pullbackTriangleIso (c.ι.app i).unop (X.map (𝟙 i)).unop
    (c.ι.app i).unop (coneSquare X c (𝟙 i))).app (F.obj i)
  have hu : e.hom ≫ (inverseImage (c.ι.app i).unop).map
      ((diagramInverseImageId X i).hom.app (F.obj i)) = 𝟙 _ := by
    simpa only [triangleCoefficientMap, diagramInverseImageId, Iso.trans_hom,
      NatTrans.comp_app, eqToIso.hom, eqToHom_app, e, Iso.app_hom] using
      triangleCoefficientMap_identity (X.map (𝟙 i)).unop
        (congrArg (fun f : X.obj i ⟶ X.obj i => f.unop) (X.map_id i))
        (c.ι.app i).unop (F.obj i)
  have he := e.hom_comp_eq_id.mp hu
  have hn := globalSectionsPullback_naturality (c.ι.app i).unop
    ((diagramInverseImageId X i).hom.app (F.obj i))
  have ht := congrArg
    (fun k : (inverseImage (c.ι.app i).unop).obj ((inverseImage (X.map (𝟙 i)).unop).obj (F.obj i)) ⟶
        (inverseImage (c.ι.app i).unop).obj (F.obj i) =>
      globalSectionsPullback (c.ι.app i).unop ((inverseImage (X.map (𝟙 i)).unop).obj (F.obj i)) ≫
        (globalSections c.pt.unop).map k) he
  exact hn.trans (ht.trans (coneArrowSectionsMap_eq_pullback X F c (Arrow.mk (𝟙 i))).symm)

lemma nativeDiagonalLeg (i : I) :
    (diagonalSectionsIso X F).inv.app i ≫ coneArrowSectionsMap X F c (Arrow.mk (𝟙 i)) =
      globalSectionsPullback (c.ι.app i).unop (F.obj i) :=
  ((diagonalSectionsIso X F).app i).inv_comp_eq.mpr
    (diagonalConeArrowSectionsMap X F c i).symm

/-- The actual comparison cocone on the original stage sections. -/
def compatibleSectionsCocone : Cocone (diagramSectionsFunctor X F) :=
  (Cocone.precompose (diagonalSectionsIso X F).inv).obj
    ((SchemeSystemColimits.outerCocone (arrowSectionsFunctor X F)
      (smallConeCoefficientSectionsFunctor X c F) (smallArrowToConeSections X F c)
      (smallConeCoefficientSectionsCocone X c F)).whisker SchemeSystemColimits.diagonal)

/-- The legs are original pullback followed by the coefficient colimit injection. -/
lemma compatibleSectionsCocone_ι (i : I) :
    (compatibleSectionsCocone X F c).ι.app i =
      sectionTransfer (c.ι.app i).unop (colimit.ι (coneCoefficientFunctor X c F) i) := by
  change (diagonalSectionsIso X F).inv.app i ≫
    (coneArrowSectionsMap X F c (Arrow.mk (𝟙 i)) ≫
      (globalSections c.pt.unop).map (colimit.ι (coneCoefficientFunctor X c F) i)) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (globalSections c.pt.unop).map
      (colimit.ι (coneCoefficientFunctor X c F) i)) (nativeDiagonalLeg X F c i))

/-- Glue supplied original fixed-coefficient tail certificates to the actual original cocone. -/
def isColimitCompatibleSectionsOfNativeTails [IsFiltered I]
    [CompactSpace c.pt.unop] [QuasiSeparatedSpace c.pt.unop]
    (h : ∀ i, IsColimit (pullbackSectionsCocone (relativeSchemeTail X i).leftOp
      (relativeSchemeTailCone X c i) (F.obj i))) :
    IsColimit (compatibleSectionsCocone X F c) :=
  (IsColimit.precomposeInvEquiv (diagonalSectionsIso X F) _).symm
    (SchemeSystemColimits.isColimitDiagonal (arrowSectionsFunctor X F)
      (smallConeCoefficientSectionsFunctor X c F) (smallArrowToConeSections X F c)
      (fun i => isColimitCompatibleTailOfNative X F c i (h i))
      (smallConeCoefficientSectionsCocone X c F) (isColimitSmallConeCoefficientSections X c F))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
