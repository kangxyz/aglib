/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Geometric
public import Aglib.Topology.Sheaves.Cohomology.OpenTransfer.CoefficientSquare

/-! # Coefficient naturality of the native geometric open-cohomology map

The original inverse-image map on the native open-Ext presheaf respects
every actual commuting coefficient square. This supplies the structural
scalar comparison for the original tensor mate on open cohomology.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- The complete original coefficient square at the underlying scheme map.
Its four edges are definitionally the native coefficient and open-transfer maps. -/
abbrev zariskiCohomologyCoefficientSquare
    {A A' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B B' : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (a : (zariskiPullback p).obj A ⟶ B) (a' : (zariskiPullback p).obj A' ⟶ B')
    (f : A ⟶ A') (g : B ⟶ B') (h : (zariskiPullback p).map f ≫ a' = a ≫ g) (n : ℕ) :=
  TopCat.Sheaf.openCohomologyCoefficientSquare.{u, u + 1} p.base a a' f g h n

/-- The original geometric open-cohomology transformation respects an actual coefficient square.
The whole native square shares its original four objects and four maps. -/
theorem zariskiCohomologyOpenMap_coefficients
    {A A' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B B' : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (a : (zariskiPullback p).obj A ⟶ B) (a' : (zariskiPullback p).obj A' ⟶ B')
    (f : A ⟶ A') (g : B ⟶ B') (h : (zariskiPullback p).map f ≫ a' = a ≫ g) (n : ℕ) :
    (zariskiCohomologyCoefficientSquare p a a' f g h n).f₁₂ ≫
        (zariskiCohomologyCoefficientSquare p a a' f g h n).f₂₄ =
      (zariskiCohomologyCoefficientSquare p a a' f g h n).f₁₃ ≫
        (zariskiCohomologyCoefficientSquare p a a' f g h n).f₃₄ :=
  (zariskiCohomologyCoefficientSquare p a a' f g h n).fac

end AlgebraicGeometry.Scheme.Cohomology
