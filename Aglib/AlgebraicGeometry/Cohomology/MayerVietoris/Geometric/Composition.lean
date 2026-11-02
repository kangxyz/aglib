/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Geometric
public import Aglib.Topology.Sheaves.FreeAbelianPullback.Composition
public import Aglib.Topology.Sheaves.Cohomology.OpenTransfer.CompositionSquare

/-! # Composition of the original geometric open-cohomology maps

Successive original inverse-image Ext maps compose to the original map for
the composite morphism, with its actual composite coefficient arrow. The
comparison of inverse-image functors is the native adjunction comparison;
the actual inverse-image opens agree definitionally.
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

variable {X Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ Y)

/-- The native inverse-image composition comparison, with the original adjunction units. -/
abbrev zariskiPullbackCompIso :
    zariskiPullback p ⋙ zariskiPullback q ≅ zariskiPullback (q ≫ p) :=
  TopCat.Sheaf.abelianPullbackCompIso p.base q.base

/-- The actual open-cohomology map uses the original native inverse-image Ext map. -/
theorem zariskiCohomologyOpenMap_app_apply
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B) (n : ℕ) (U : X.Opensᵒᵖ)
    (x : Ext.{u + 1} ((additiveOpenFreeFunctor X).obj U.unop) A n) :
    (zariskiCohomologyOpenMap p A B a n).app U x =
      ((Ext.mk₀ ((additiveOpenPullbackIso p).inv.app U.unop)).comp
        (x.mapExactFunctor (zariskiPullback p)) (Nat.zero_add n)).comp
          (Ext.mk₀ a) (Nat.add_zero n) := rfl

/-- The complete native composition triangle, with its original three maps
and canonical composite coefficient, viewed as a square with an identity edge. -/
abbrev zariskiCohomologyCompositionSquare
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (C : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B)
    (b : (zariskiPullback q).obj B ⟶ C) (n : ℕ) :=
  TopCat.Sheaf.openCohomologyCompositionSquare.{u, u + 1} p.base q.base a b n

/-- The original geometric open-cohomology transformation respects composition.
The displayed projections are the same original three native maps. -/
theorem zariskiCohomologyOpenMap_comp
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (C : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B)
    (b : (zariskiPullback q).obj B ⟶ C) (n : ℕ) :
    (zariskiCohomologyCompositionSquare p q A B C a b n).f₁₂ ≫
        (zariskiCohomologyCompositionSquare p q A B C a b n).f₂₄ =
      (zariskiCohomologyCompositionSquare p q A B C a b n).f₁₃ :=
  TopCat.Sheaf.openCohomologyCompositionSquare_comp.{u, u + 1} p.base q.base a b n

/-- Successive original geometric maps on an open are the original composite map,
with its actual inverse-image composite coefficient. -/
theorem zariskiCohomologyOpenMap_comp_app
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (C : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B)
    (b : (zariskiPullback q).obj B ⟶ C) (n : ℕ) (U : X.Opensᵒᵖ) :
    (zariskiCohomologyCompositionSquare p q A B C a b n).f₁₂.app U ≫
        (zariskiCohomologyCompositionSquare p q A B C a b n).f₂₄.app U =
      (zariskiCohomologyCompositionSquare p q A B C a b n).f₁₃.app U :=
  TopCat.Sheaf.openCohomologyCompositionSquare_comp_app.{u, u + 1} p.base q.base a b n U

end AlgebraicGeometry.Scheme.Cohomology
