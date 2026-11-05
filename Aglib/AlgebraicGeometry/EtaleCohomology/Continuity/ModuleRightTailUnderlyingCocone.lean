/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleUnderlyingColimit

/-! # Original right-tail cocones after forgetting scalars

The canonical coefficient-colimit comparison intertwines the actual adjunct
legs and actual right triangles. Thus this compares whole original cocones,
not merely their objectwise diagrams or their colimit objects.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

universe u r uI vI

variable (R : Type r) [Ring R] {I : Type uI} [Category.{vI} I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (F : DiagramCoefficientSystem R X)

attribute [local instance] ModuleCat.Sheaf.hasSheafify hasSheafifyLarge

variable [hM : HasColimit (coneCoefficientFunctor R X c F)]
    [HasColimit (Continuity.coneCoefficientFunctor X c (underlyingSystem R X F))]
    [PreservesColimit (coneCoefficientFunctor R X c F) (underlying R c.pt.unop)]

local instance nativeRightTailConeHasColimit :
    HasColimit ((diagramConeAdjunctionData R X c).coefficientFunctor F) := hM

/-- Every original abelian right-tail leg followed by the actual apex
comparison is the scalar-forgetting image of the native leg. -/
@[reassoc]
theorem rightTailLeg_underlying (i : I) (a : Under i) :
    (Continuity.diagramRightTailCocone X (underlyingSystem R X F) c i).ι.app a ≫
        (EtaleCohomology.directImage (c.ι.app i).unop).map
          (coefficientColimitUnderlyingIso R X c F).hom =
      (underlying R (X.obj i).unop).map ((diagramRightTailCocone R X c F i).ι.app a) := by
  let PA := Continuity.diagramConeAdjunctionData X c
  let PM := diagramConeAdjunctionData R X c
  let e := coefficientColimitUnderlyingIso R X c F
  rw [Continuity.diagramRightTailCocone_ι_app, Category.assoc]
  change (EtaleCohomology.directImage (X.map a.hom).unop).map
      (Continuity.diagramAdjointLeg X c (underlyingSystem R X F) a.right) ≫
      (PA.rightTriangle a.hom).hom.app
        (colimit (Continuity.coneCoefficientFunctor X c (underlyingSystem R X F))) ≫
      (EtaleCohomology.directImage (c.ι.app i).unop).map e.hom = _
  erw [← (PA.rightTriangle a.hom).hom.naturality e.hom]
  change (EtaleCohomology.directImage (X.map a.hom).unop).map
      (Continuity.diagramAdjointLeg X c (underlyingSystem R X F) a.right) ≫
      (EtaleCohomology.directImage (X.map a.hom).unop).map
        ((EtaleCohomology.directImage (c.ι.app a.right).unop).map e.hom) ≫
      (PA.rightTriangle a.hom).hom.app _ = _
  erw [← Functor.map_comp_assoc, adjointLeg_underlying R X c F a.right]
  erw [← underlying_cone_rightTriangle_hom R X c a.hom
    (colimit (coneCoefficientFunctor R X c F))]
  change (underlying R (X.obj i).unop).map
      ((directImage R (X.map a.hom).unop).map (PM.adjointLeg F a.right)) ≫
      (underlying R (X.obj i).unop).map ((PM.rightTriangle a.hom).hom.app _) = _
  erw [← Functor.map_comp]
  rfl

/-- The complete original right-tail cocones agree under the canonical
coefficient-colimit comparison and the original underlying diagram isomorphism. -/
def rightTailUnderlyingCoconeIso (i : I) :
    (Cocone.precompose (rightTailUnderlyingIso R X F i).hom).obj
        (Continuity.diagramRightTailCocone X (underlyingSystem R X F) c i) ≅
      (underlying R (X.obj i).unop).mapCocone (diagramRightTailCocone R X c F i) := by
  refine Cocone.ext ((EtaleCohomology.directImage (c.ι.app i).unop).mapIso
    (coefficientColimitUnderlyingIso R X c F)) (fun a => ?_)
  change (𝟙 _) ≫
      (Continuity.diagramRightTailCocone X (underlyingSystem R X F) c i).ι.app a ≫
      (EtaleCohomology.directImage (c.ι.app i).unop).map
        (coefficientColimitUnderlyingIso R X c F).hom =
    (underlying R (X.obj i).unop).map ((diagramRightTailCocone R X c F i).ι.app a)
  simpa only [Category.id_comp] using rightTailLeg_underlying R X c F i a

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
