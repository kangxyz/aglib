/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackCohomologyNormalization

/-! # The original fixed-coefficient limit cocone

The apex is cohomology of the original structural inverse image. No continuity or
colimit certificate for this cohomology cocone is asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u e uI vI
attribute [local instance] hasSheafifyLarge
open Continuity

variable {I : Type uI} [Category.{vI} I] (Y : I ⥤ Scheme.{u}ᵒᵖ)
  (b : Cone Y) (c : Cocone Y) (l : b.pt ⟶ c.pt)
  (hl : ∀ i, b.π.app i ≫ c.ι.app i = l)
  (F : AbelianSheaf.{u, u + 1} b.pt.unop)
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (Y.obj i).unop)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [IsConnected I]
  [HasColimit (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F))]

/-- Apply original cohomology to the actual fixed-coefficient colimit identification. -/
def pullbackLimitCohomologyIso (q : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{e}
        (colimit (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F))) q) ≅
      AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage l.unop).obj F) q) :=
  (Sheaf.functorH (Scheme.smallEtaleTopology c.pt.unop) q).mapIso
    (pullbackLimitCoefficientIso Y b c l hl F)

/-- Extend the actual system cocone to the original structural pullback coefficient. -/
def pullbackLimitCohomologyCocone (q : ℕ) :
    Cocone (diagramCohomologyFunctor Y (pullbackCoefficientSystem Y b F) q) :=
  (diagramCohomologyCocone Y c (pullbackCoefficientSystem Y b F) q).extend
    (pullbackLimitCohomologyIso Y b c l hl F q).hom

/-- Each normalized leg is the original cohomological structural pullback. -/
theorem pullbackLimitCohomologyCocone_leg (q : ℕ) (i : I) :
    (pullbackLimitCohomologyCocone Y b c l hl F q).ι.app i =
      cohomologyTransfer (X := (Y.obj i).unop) (Y := c.pt.unop) (c.ι.app i).unop
        ((pullbackTriangleIso l.unop (b.π.app i).unop (c.ι.app i).unop
          (congrArg Quiver.Hom.unop (hl i))).inv.app F) q :=
  diagramCohomologyLeg_pullbackLimitCoefficientIso Y b c l hl F q i

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
