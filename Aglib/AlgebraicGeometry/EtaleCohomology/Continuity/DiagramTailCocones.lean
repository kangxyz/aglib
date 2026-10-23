/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTailSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSmallIndex

/-! # Original relative section cocones and the compatible-system tail cocone

These are transports of actual cocones. No fixed-coefficient scheme-limit
continuity certificate is supplied by this file.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge
variable {I : Type u} [Category.{u} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (c : Cocone X) (i : I)

/-- The actual η natural transformation with the geometry theorem's original index size. -/
def smallArrowToConeSections : arrowSectionsFunctor X F ⟶
    Arrow.leftFunc ⋙ smallConeCoefficientSectionsFunctor X c F where
  app a := coneArrowSectionsMap X F c a
  naturality a _ m :=
    (coneArrowSectionsMap_naturality X F c m).trans
      (congrArg (fun k => coneArrowSectionsMap X F c a ≫ k)
        (coneSystemSectionsMap_eq X F c m.left))

/-- The original relative section cocone, indexed directly by the actual tail. -/
def relativeTailSectionsCocone :
    Cocone (relativeSchemeTail X i ⋙ pullbackSectionsFunctor (F.obj i)) :=
  (pullbackSectionsFunctor (F.obj i)).mapCocone (relativeSchemeTailCocone X c i)

/-- Remove only the double-opposite indexing from the geometry theorem's native cone form. -/
def isColimitRelativeTailSectionsOfNative
    (h : IsColimit (pullbackSectionsCocone (relativeSchemeTail X i).leftOp
      (relativeSchemeTailCone X c i) (F.obj i))) :
    IsColimit (relativeTailSectionsCocone X F c i) := by
  exact (Functor.Final.isColimitWhiskerEquiv (opOp (Under i)) _).symm h

/-- The canonical tail of η, retaining its original coefficient comparison legs. -/
def compatibleTailSectionsCocone :
    Cocone (SchemeSystemColimits.tailToArrow i ⋙ arrowSectionsFunctor X F) :=
  SchemeSystemColimits.tailCocone (arrowSectionsFunctor X F)
    (smallConeCoefficientSectionsFunctor X c F) (smallArrowToConeSections X F c) i

/-- The original relative section cocone is the canonical tail cocone after diagram transport. -/
def relativeTailSectionsCoconeIso :
    (Cocone.precompose (relativeTailSectionsIso X F i).hom).obj
      (relativeTailSectionsCocone X F c i) ≅ compatibleTailSectionsCocone X F c i := by
  refine Cocone.ext (Iso.refl _) (fun a => ?_)
  change (𝟙 _ ≫ pullbackSectionsMap (F.obj i)
    (coneArrowOverHom X c (Arrow.mk a.hom))) ≫ 𝟙 _ =
      coneArrowSectionsMap X F c (Arrow.mk a.hom)
  exact (Category.comp_id _).trans ((Category.id_comp _).trans
    (coneArrowSectionsMap_eq_pullback X F c (Arrow.mk a.hom)).symm)

/-- Transport a supplied native geometric certificate, without asserting that it exists. -/
def isColimitCompatibleTailOfNative
    (h : IsColimit (pullbackSectionsCocone (relativeSchemeTail X i).leftOp
      (relativeSchemeTailCone X c i) (F.obj i))) :
    IsColimit (compatibleTailSectionsCocone X F c i) :=
  IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (relativeTailSectionsIso X F i) _).symm
      (isColimitRelativeTailSectionsOfNative X F c i h))
    (relativeTailSectionsCoconeIso X F c i)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
