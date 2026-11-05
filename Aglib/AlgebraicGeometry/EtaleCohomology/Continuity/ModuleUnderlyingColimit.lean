/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleUnderlyingCone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramAdjointCocone
public import Aglib.Algebra.Category.ModuleCat.Sheaf.UnderlyingColimits

/-! # The original coefficient colimit and its adjuncts after forgetting scalars

The comparison is the canonical colimit comparison of the original diagram
isomorphism and the original scalar-forgetting functor. Its insertion and
adjunction equations retain the actual coefficient-colimit legs.
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

local instance nativeConeHasColimit :
    HasColimit ((diagramConeAdjunctionData R X c).coefficientFunctor F) := hM

/-- The canonical comparison of the original abelian and native coefficient colimits. -/
def coefficientColimitUnderlyingIso :
    colimit (Continuity.coneCoefficientFunctor X c (underlyingSystem R X F)) ≅
      (underlying R c.pt.unop).obj (colimit (coneCoefficientFunctor R X c F)) :=
  HasColimit.isoOfNatIso (coneCoefficientUnderlyingIso R X c F) ≪≫
    (preservesColimitIso (underlying R c.pt.unop) (coneCoefficientFunctor R X c F)).symm

/-- Original coefficient-colimit injections commute with the comparison. -/
@[reassoc]
theorem coefficientColimitUnderlyingIso_ι (i : I) :
    colimit.ι (Continuity.coneCoefficientFunctor X c (underlyingSystem R X F)) i ≫
        (coefficientColimitUnderlyingIso R X c F).hom =
      (coneCoefficientUnderlyingIsoApp R X c F i).hom ≫
        (underlying R c.pt.unop).map (colimit.ι (coneCoefficientFunctor R X c F) i) := by
  simp only [coefficientColimitUnderlyingIso, Iso.trans_hom, Iso.symm_hom,
    HasColimit.ι_isoOfNatIso_hom_assoc, ι_preservesColimitIso_inv,
    coneCoefficientUnderlyingIso]
  rfl

/-- The actual adjunct of each original injection commutes with scalar forgetting. -/
@[reassoc]
theorem adjointLeg_underlying (i : I) :
    Continuity.diagramAdjointLeg X c (underlyingSystem R X F) i ≫
        (EtaleCohomology.directImage (c.ι.app i).unop).map
          (coefficientColimitUnderlyingIso R X c F).hom =
      (underlying R (X.obj i).unop).map
        ((diagramConeAdjunctionData R X c).adjointLeg F i) := by
  change (inverseImageAdjunction (c.ι.app i).unop).homEquiv _ _
      (colimit.ι (Continuity.coneCoefficientFunctor X c (underlyingSystem R X F)) i) ≫ _ = _
  rw [← Adjunction.homEquiv_naturality_right, coefficientColimitUnderlyingIso_ι]
  exact (underlying_homEquiv R (c.ι.app i).unop (F.obj i)
    (colimit (coneCoefficientFunctor R X c F))
    (colimit.ι (coneCoefficientFunctor R X c F) i)).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
