/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModuleCohomologyComparison
public import Aglib.Algebra.Homology.DerivedCategory.Ext.AdjunctionPostcomp

/-! # Original forward map of the native module cohomology comparison

The existing equivalence is expressed through its original value lift, exact
inverse image and native coefficient adjunct. No new cohomology construction
or additional resolution is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open CategoryTheory.Sheaf.BasisAcyclicity

universe u e e'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

/-- The original module coefficient comparison, transposed through the unchanged
Zariski--étale adjunction. -/
def moduleCoefficientComparison (X : Scheme.{u}) (M : X.Modules) [M.IsQuasicoherent] :
    (zariskiInverseImage X).obj
      ((valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology X)).obj
        (Scheme.Cohomology.moduleAddSheaf X M)) ⟶ additiveCoefficient X M :=
  ((zariskiEtaleAdjunction X).homEquiv _ _).symm (zariskiModuleIso X M).inv

/-- The original inverse coefficient is the whole unit followed by this actual adjunct. -/
@[reassoc]
theorem moduleCoefficientComparison_unit (X : Scheme.{u}) (M : X.Modules)
    [M.IsQuasicoherent] :
    (zariskiEtaleAdjunction X).unit.app
        ((valueLift.{u, u, u, u + 1} (Opens.grothendieckTopology X)).obj
          (Scheme.Cohomology.moduleAddSheaf X M)) ≫
      (zariskiRestriction X).map (moduleCoefficientComparison X M) =
        (zariskiModuleIso X M).inv :=
  ((zariskiEtaleAdjunction X).homEquiv_unit
    (f := moduleCoefficientComparison X M)).symm.trans
      (((zariskiEtaleAdjunction X).homEquiv _ _).apply_symm_apply _)

variable (X : Scheme.{u})
  [HasExt.{e} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{e'} (AbelianSheaf.{u, u + 1} X)]

/-- Forward-map normalization of the unchanged absolute comparison. Its first
leg is the original value-lift cohomology map, its last is the original adjunct,
and the constant-integer source map is the native site-pullback comparison. -/
theorem moduleCohomologyComparison_apply_adjunct
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Sheaf.H.{e} (Scheme.Cohomology.moduleAddSheaf X M) n) :
    moduleCohomologyComparison X M n x =
      (Ext.mk₀ (Sheaf.Hypercohomology.pullbackConstantIntegerIso.{u, u, u + 1, u, u + 1}
        (opensToEtale X) (Opens.grothendieckTopology X) (smallEtaleTopology X)
        ⊤ isTerminalTop (opensToEtaleTopIsTerminal X)).inv).comp
        (((valueLiftCohomologyMap.{e, u + 2, u, u, u, u + 1} isTerminalTop
          (Scheme.Cohomology.moduleAddSheaf X M) n x).mapExactFunctor (zariskiInverseImage X)).comp
          (Ext.mk₀ (moduleCoefficientComparison X M)) (Nat.add_zero n)) (Nat.zero_add n) := by
  change (Ext.mk₀ (Sheaf.Hypercohomology.pullbackConstantIntegerIso.{u, u, u + 1, u, u + 1}
      (opensToEtale X) (Opens.grothendieckTopology X) (smallEtaleTopology X)
      ⊤ isTerminalTop (opensToEtaleTopIsTerminal X)).inv).comp
    ((zariskiEtaleAdjunction X).extCounitMap _ _ n
      ((valueLiftCohomologyMap.{e, u + 2, u, u, u, u + 1} isTerminalTop
        (Scheme.Cohomology.moduleAddSheaf X M) n x).comp
        (Ext.mk₀ (zariskiModuleIso X M).inv) (Nat.add_zero n))) (Nat.zero_add n) = _
  rw [Adjunction.extCounitMap_postcomp]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
