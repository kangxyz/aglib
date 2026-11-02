/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModuleValueLiftPullback
public import Aglib.Topology.Sheaves.AbelianPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiPullbackConstant
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLiftPullbackCoefficientCohomology

/-! # Original Zariski cohomology pullback through the genuine value lift -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open CategoryTheory.Sheaf.BasisAcyclicity CategoryTheory.Sheaf.Hypercohomology
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local instance raisedOpensPullbackExact :
    PreservesFiniteLimits ((Opens.map f.base).sheafPullback AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
  TopCat.Sheaf.opensAbelianPullback_preservesFiniteLimits.{u, u + 1} f.base

local instance raisedOpensPullbackAdditive :
    ((Opens.map f.base).sheafPullback AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).Additive :=
  TopCat.Sheaf.opensAbelianPullback_additive.{u, u + 1} f.base

local instance raisedOpensPullbackColimits :
    PreservesFiniteColimits ((Opens.map f.base).sheafPullback AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) := by
  let := ((Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).isLeftAdjoint
  infer_instance

local instance smallOpensPullbackExact :
    PreservesFiniteLimits ((Opens.map f.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
  TopCat.Sheaf.opensAbelianPullback_preservesFiniteLimits.{u, u} f.base

local instance smallOpensPullbackAdditive :
    ((Opens.map f.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).Additive :=
  TopCat.Sheaf.opensAbelianPullback_additive.{u, u} f.base

local instance smallOpensPullbackColimits :
    PreservesFiniteColimits ((Opens.map f.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) := by
  let := ((Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).isLeftAdjoint
  infer_instance

/-- The original Zariski cohomology map commutes with the actual value lift,
including an arbitrary coefficient arrow. Module coefficients are supplied only
after this whole original-map law has been proved. -/
theorem zariskiCohomologyMap_valueLift
    (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (H : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (g : (Scheme.Cohomology.zariskiPullback f).obj F ⟶ H)
    (n : ℕ) (x : Sheaf.H.{u + 1} F n) :
    valueLiftCohomologyMap.{u + 1, u + 2, u, u, u, u + 1} isTerminalTop H n
      (Scheme.Cohomology.zariskiCohomologyMap f F H g n x) =
    (((Opens.map f.base).sheafPullback AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).extPrecompMap
        (pullbackConstantIntegerIso.{u, u, u, u, u + 1} (Opens.map f.base)
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
          ⊤ isTerminalTop (opensMapTopIsTerminal f)).inv
        ((valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology Y)).obj F) n
        (valueLiftCohomologyMap.{u + 1, u + 2, u, u, u, u + 1} isTerminalTop F n x)).comp
      (Ext.mk₀ ((valueLiftPullbackMap.{u, u, u, u, u, u + 1} (Opens.map f.base)
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).app F ≫
          (valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology X)).map g))
      (Nat.add_zero n) := by
  have h := valueLiftPullbackMap_cohomology_comp.{u, u, u, u, u, u + 1,
      u + 1, u + 2, u + 1, u + 2}
    (Opens.map f.base) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    ⊤ isTerminalTop (opensMapTopIsTerminal f) F H g n x
  rw [opensPullbackConstantIntegerIso_inv] at h
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
