/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramNativeCocone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeNaturality

/-! # Naturality of the original compatible-system comparison cocone -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge
variable {I : Type u} [Category.{u} I] (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)
  {F G : DiagramCoefficientSystem X}
  (η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F G)

/-- The original comparison legs commute with the actual map of coefficient colimits. -/
lemma compatibleSectionsCocone_naturality (i : I) :
    (globalSections (X.obj i).unop).map (η.app i) ≫
        (compatibleSectionsCocone X G c).ι.app i =
      (compatibleSectionsCocone X F c).ι.app i ≫
        (globalSections c.pt.unop).map (coneCoefficientColimitMap X c η) := by
  rw [compatibleSectionsCocone_ι, compatibleSectionsCocone_ι]
  exact (sectionTransfer_naturality (c.ι.app i).unop
    (colimit.ι (coneCoefficientFunctor X c F) i)
    (colimit.ι (coneCoefficientFunctor X c G) i)
    (η.app i) (coneCoefficientColimitMap X c η)
    (coneCoefficientColimitMap_ι X c η i).symm).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
