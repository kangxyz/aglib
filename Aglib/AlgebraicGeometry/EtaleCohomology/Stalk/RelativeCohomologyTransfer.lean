/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem

/-! # Original cohomological restriction along actual relative scheme morphisms -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u e
attribute [local instance] hasSheafifyLarge
open Continuity
variable {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
  {A B C : Over X}
  [HasExt.{e} (AbelianSheaf.{u, u + 1} A.left)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} B.left)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} C.left)]

/-- Pullback along an actual relative arrow, with its original coefficient triangle. -/
def relativeCohomologyTransfer (a : A ⟶ B) :
    AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage B.hom).obj F) q) ⟶
      AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage A.hom).obj F) q) :=
  cohomologyTransfer a.left
    ((pullbackTriangleIso A.hom B.hom a.left (Over.w a)).inv.app F) q

/-- Original relative cohomology respects the actual composite relative arrow. -/
theorem relativeCohomologyTransfer_comp (a : A ⟶ B) (b : B ⟶ C) :
    relativeCohomologyTransfer F q b ≫ relativeCohomologyTransfer F q a =
      relativeCohomologyTransfer F q (a ≫ b) := by
  exact (cohomologyTransfer_comp b.left a.left
    ((pullbackTriangleIso B.hom C.hom b.left (Over.w b)).inv.app F)
    ((pullbackTriangleIso A.hom B.hom a.left (Over.w a)).inv.app F) q).trans
    (congrArg (fun φ => cohomologyTransfer (a.left ≫ b.left) φ q)
      (pullbackTriangleIso_comp_inv C.hom B.hom A.hom a.left b.left
        (Over.w b) (Over.w a) F))

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
