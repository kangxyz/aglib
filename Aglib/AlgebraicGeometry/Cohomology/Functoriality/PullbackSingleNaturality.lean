/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PullbackSingle
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.SingleComparison

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalGenerationEndpoints.lean` at
LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: cut_general;
source ranges [[39, 56], [66, 89]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived category of module sheaves used for single-object pullback naturality. -/
local instance pullbackSingleNaturalityStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

theorem derivedFlatPullbackPlusSingleIso_naturality {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] {M N : Y.Modules} (g : M ⟶ N) :
    (derivedFlatPullbackPlus f).map ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map g) ≫
      (derivedFlatPullbackPlusSingleIso f N).hom =
    (derivedFlatPullbackPlusSingleIso f M).hom ≫
      (DerivedCategory.Plus.singleFunctor X.Modules 0).map ((Scheme.Modules.pullback f).map g) := by
  simpa [exactDerivedSingleNatIso, exactSingleComplexNatIso,
    derivedFlatPullbackPlusSingleIso, pullbackSingleZeroPlusIso, derivedFlatPullbackPlus,
      flatExactPullback] using
      (exactDerivedSingleNatIso (Scheme.Modules.pullback f)).hom.naturality g

end AlgebraicGeometry.Scheme.Modules
