/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Identity

/-! # Identity for bounded-below derived geometric pullback

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/NativeProjectionPerfect.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`afe81abde71858d5f16de1d8cdb3a69d2c80e50de7ac710eb5b9860fa1d94361`.
Selected declarations: derivedFlatPullbackPlusIdIso.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- The standard derived category of module sheaves used for the identity pullback comparison. -/
local instance identityPullbackDerivedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The bounded-below derived pullback along the identity, identified with the identity functor. -/
def derivedFlatPullbackPlusIdIso (X : Scheme.{u}) :
    derivedFlatPullbackPlus (𝟙 X) ≅ 𝟭 (DerivedCategory.Plus X.Modules) :=
  (Scheme.Modules.pullback (𝟙 X)).rightDerivedFunctorPlusIso
    (Scheme.Modules.pullbackId X) ≪≫ Functor.rightDerivedFunctorPlusIdIso X.Modules

end AlgebraicGeometry.Scheme.Modules
