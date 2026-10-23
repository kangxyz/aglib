/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomologyCocone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeNaturality

/-! # Coefficient naturality of the original all-degree scheme-limit comparison -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u e uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  (c : Cocone X) [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [HasColimitsOfShape I (AbelianSheaf.{u, u + 1} c.pt.unop)]
  {F G : DiagramCoefficientSystem X}
  (η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F G) (n : ℕ)

lemma diagramCohomologyLeg_coefficient_naturality (i : I) :
    diagramCohomologyLeg X c F n i ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (coneCoefficientColimitMap X c η) n) =
      AddCommGrpCat.ofHom (Sheaf.H.map (η.app i) n) ≫ diagramCohomologyLeg X c G n i :=
  cohomologyTransfer_naturality (X := (X.obj i).unop) (Y := c.pt.unop)
    (c.ι.app i).unop (colimit.ι (coneCoefficientFunctor X c F) i)
    (colimit.ι (coneCoefficientFunctor X c G) i) (η.app i)
    (coneCoefficientColimitMap X c η) (coneCoefficientColimitMap_ι X c η i).symm n

variable [HasColimitsOfShape I AddCommGrpCat.{e}]

/-- Naturality uses the original system and coefficient colimit morphisms on both sides. -/
lemma schemeLimitCohomologyComparison_naturality :
    colim.map (diagramCohomologyNatTrans X n η) ≫
        schemeLimitCohomologyComparison X c G n =
      schemeLimitCohomologyComparison X c F n ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (coneCoefficientColimitMap X c η) n) := by
  apply colimit.hom_ext
  intro i
  rw [colimit.ι_map_assoc, ι_schemeLimitCohomologyComparison,
    ι_schemeLimitCohomologyComparison_assoc]
  exact (diagramCohomologyLeg_coefficient_naturality X c η n i).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
