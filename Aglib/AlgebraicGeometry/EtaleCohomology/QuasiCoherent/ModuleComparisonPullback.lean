/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModuleComparisonMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiPullbackSquare
public import Aglib.CategoryTheory.Adjunction.SquareCoefficient

/-! # Geometric naturality of the original module coefficient adjunct

The raised Zariski arrow is the adjunct of the lifted native module unit.
The geometric square uses the original composite inverse-image comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace
open CategoryTheory.Sheaf.BasisAcyclicity
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent]

omit [M.IsQuasicoherent] in
/-- The actual raised-value Zariski adjunct of the original module unit. -/
def raisedModulePullback :
    ((Opens.map f.base).sheafPullback AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
        ((valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology Y)).obj
          (Scheme.Cohomology.moduleAddSheaf Y M)) ⟶
      (valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology X)).obj
        (Scheme.Cohomology.moduleAddSheaf X ((pullback f).obj M)) :=
  (((Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).homEquiv _ _).symm
      ((valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology Y)).map
        ((SheafOfModules.toSheaf Y.ringCatSheaf).map
          ((pullbackPushforwardAdjunction f).unit.app M)))

/-- Geometric naturality before cohomology, for arbitrary scheme morphisms.
No flatness of the morphism or of Frobenius is asserted or needed. -/
theorem moduleCoefficientComparison_pullback :
    (inverseImage f).map (moduleCoefficientComparison Y M) ≫
        additiveCoefficientPullback f M =
      (zariskiInverseImagePullbackIso f).hom.app
        ((valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology Y)).obj
          (Scheme.Cohomology.moduleAddSheaf Y M)) ≫
        (zariskiInverseImage X).map (raisedModulePullback f M) ≫
          moduleCoefficientComparison X ((pullback f).obj M) := by
  apply Adjunction.coefficient_square_of_homEquiv
    (zariskiEtaleAdjunction Y) (zariskiEtaleAdjunction X)
    ((Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
    (inverseImageAdjunction f) (zariskiRestrictionDirectImageIso f)
  simp only [moduleCoefficientComparison, additiveCoefficientPullback,
    raisedModulePullback, Equiv.apply_symm_apply]
  change (zariskiModuleIso Y M).inv ≫
    (zariskiRestriction Y).map (additiveCoefficientPullbackUnit f M) ≫
      (zariskiRestrictionDirectImageIso f).hom.app
        (additiveCoefficient X ((pullback f).obj M)) =
    (valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology Y)).map
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map
        ((pullbackPushforwardAdjunction f).unit.app M)) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u + 1} f.base).map
        (zariskiModuleIso X ((pullback f).obj M)).inv
  apply (cancel_mono ((TopCat.Sheaf.pushforward AddCommGrpCat.{u + 1} f.base).map
    (zariskiModuleIso X ((pullback f).obj M)).hom)).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  rw [zariskiModuleIso_pullbackUnit, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
  rw [(TopCat.Sheaf.pushforward AddCommGrpCat.{u + 1} f.base).map_id]
  exact (Category.comp_id
    ((valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology Y)).map
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map
        ((pullbackPushforwardAdjunction f).unit.app M)))).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
