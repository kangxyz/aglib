/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModuleComparisonPullback
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLiftPullback
public import Aglib.CategoryTheory.Adjunction.UnderlyingHomEquiv

/-! # The original module coefficient map through value lift

The actual raised adjunct factors through the native value-lift mate and the
unchanged additive module coefficient arrow. This does not assert that the
value-lift mate is invertible.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace
open CategoryTheory.Sheaf.BasisAcyclicity
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

/-- Original coefficient compatibility of value lift with geometric pullback. -/
theorem raisedModulePullback_eq_valueLift :
    raisedModulePullback f M =
      (valueLiftPullbackMap.{u, u, u, u, u, u + 1} (Opens.map f.base)
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).app
          (Scheme.Cohomology.moduleAddSheaf Y M) ≫
        (valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology X)).map
          (Scheme.Cohomology.moduleCoefficientPullback f
            ((pullbackPushforwardAdjunction f).unit.app M)) := by
  let a := (Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  let b := (Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  let d := valueLiftDirectImageIso.{u, u, u, u, u, u + 1} (Opens.map f.base)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  have h := underlying_homEquiv_of_mate a b
    ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ d.hom)) d.hom
    (by simp only [Equiv.apply_symm_apply])
    (Scheme.Cohomology.moduleAddSheaf Y M)
    (Scheme.Cohomology.moduleAddSheaf X ((pullback f).obj M))
    (Scheme.Cohomology.moduleCoefficientPullback f
      ((pullbackPushforwardAdjunction f).unit.app M))
  let g := Scheme.Cohomology.moduleCoefficientPullback f
    ((pullbackPushforwardAdjunction f).unit.app M)
  have hg : a.homEquiv _ _ g =
      (SheafOfModules.toSheaf Y.ringCatSheaf).map
        ((pullbackPushforwardAdjunction f).unit.app M) := by
    change (a.homEquiv _ _) ((a.homEquiv _ _).symm (_ ≫ 𝟙 _)) = _
    rw [Equiv.apply_symm_apply, Category.comp_id]
  change (valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology Y)).map
      (a.homEquiv _ _ g) ≫ 𝟙 _ =
    b.homEquiv _ _
      ((valueLiftPullbackMap.{u, u, u, u, u, u + 1} (Opens.map f.base)
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).app
          (Scheme.Cohomology.moduleAddSheaf Y M) ≫
        (valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology X)).map g) at h
  rw [hg, Category.comp_id] at h
  apply (b.homEquiv _ _).injective
  change b.homEquiv _ _ ((b.homEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply]
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
