/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackCohomologyCocone

/-! # Original structural transfer with the actual fixed-system cohomology source -/

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

/-- Original cohomological pullback along a limit arrow and its structural triangle.
The source is the original system group, not a separately reconstructed coefficient model. -/
def pullbackLimitCohomologyLeg (q : ℕ) (i : I) :
    diagramCohomologyObj Y (pullbackCoefficientSystem Y b F) q i ⟶
      AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage l.unop).obj F) q) :=
  cohomologyTransfer (X := (Y.obj i).unop) (Y := c.pt.unop) (c.ι.app i).unop
    ((pullbackTriangleIso l.unop (b.π.app i).unop (c.ι.app i).unop
      (congrArg Quiver.Hom.unop (hl i))).inv.app F) q

variable [IsConnected I]
  [HasColimit (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F))]

/-- Identify complete original morphisms before specializing a geometric limit. -/
theorem pullbackLimitCohomologyCocone_leg_eq (q : ℕ) (i : I) :
    (pullbackLimitCohomologyCocone Y b c l hl F q).ι.app i =
      pullbackLimitCohomologyLeg Y b c l hl F q i :=
  pullbackLimitCohomologyCocone_leg Y b c l hl F q i

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
