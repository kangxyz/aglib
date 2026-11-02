/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cohomology.OpenTransfer
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.CompositionSquare

/-! # The complete original open-cohomology composition triangle

Specialize the complete original Ext-diagram triangle, including its three
transfer maps, original composite coefficient and native source coherence.
The fourth square edge is only the identity; no auxiliary cohomology model
or additional composition premise is introduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X Y Z : TopCat.{u}}
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})]

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms

local instance (p : Y ⟶ X) : (openCohomologyInverseImage p).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction AddCommGrpCat.{u} p).isLeftAdjoint

local instance (p : Y ⟶ X) : RepresentablyFlat (Opens.map p) :=
  flat_of_preservesFiniteLimits _

local instance (p : Y ⟶ X) : PreservesFiniteLimits (openCohomologyInverseImage p) := by
  change PreservesFiniteLimits ((Opens.map p).sheafPullback AddCommGrpCat.{u} _ _)
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

local instance (p : Y ⟶ X) : (openCohomologyInverseImage p).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The complete original composition triangle, represented as a square with
an identity bottom edge and the original composite coefficient arrow. -/
def openCohomologyCompositionSquare (p : Y ⟶ X) (q : Z ⟶ Y)
    {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    {C : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}}
    (a : (openCohomologyInverseImage p).obj A ⟶ B)
    (b : (openCohomologyInverseImage q).obj B ⟶ C) (n : ℕ) :
    Square ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  (openCohomologyInverseImage p).extDiagramCompositionSquare
    (openCohomologyInverseImage q) (openCohomologyInverseImage (q ≫ p))
    (abelianPullbackCompIso p q).symm
    (openFreeAbelianFunctor X) (openFreeAbelianFunctor Y) (openFreeAbelianFunctor Z)
    (Opens.map p) (Opens.map q)
    (openFreeAbelianPullbackIso p) (openFreeAbelianPullbackIso q)
    (openFreeAbelianPullbackIso (q ≫ p))
    (fun U => (openFreeAbelianPullbackIso_comp_inv p q U).symm) a b n

/-- The whole original composition equation of the complete triangle. -/
theorem openCohomologyCompositionSquare_comp (p : Y ⟶ X) (q : Z ⟶ Y)
    {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    {C : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}}
    (a : (openCohomologyInverseImage p).obj A ⟶ B)
    (b : (openCohomologyInverseImage q).obj B ⟶ C) (n : ℕ) :
    (openCohomologyCompositionSquare p q a b n).f₁₂ ≫
        (openCohomologyCompositionSquare p q a b n).f₂₄ =
      (openCohomologyCompositionSquare p q a b n).f₁₃ :=
  (openCohomologyInverseImage p).extDiagramCompositionSquare_comp
    (openCohomologyInverseImage q) (openCohomologyInverseImage (q ≫ p))
    (abelianPullbackCompIso p q).symm
    (openFreeAbelianFunctor X) (openFreeAbelianFunctor Y) (openFreeAbelianFunctor Z)
    (Opens.map p) (Opens.map q)
    (openFreeAbelianPullbackIso p) (openFreeAbelianPullbackIso q)
    (openFreeAbelianPullbackIso (q ≫ p))
    (fun U => (openFreeAbelianPullbackIso_comp_inv p q U).symm) a b n

/-- The original composition equation at each open, from the same triangle. -/
theorem openCohomologyCompositionSquare_comp_app (p : Y ⟶ X) (q : Z ⟶ Y)
    {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    {C : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}}
    (a : (openCohomologyInverseImage p).obj A ⟶ B)
    (b : (openCohomologyInverseImage q).obj B ⟶ C) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    (openCohomologyCompositionSquare p q a b n).f₁₂.app U ≫
        (openCohomologyCompositionSquare p q a b n).f₂₄.app U =
      (openCohomologyCompositionSquare p q a b n).f₁₃.app U :=
  (openCohomologyInverseImage p).extDiagramCompositionSquare_comp_app
    (openCohomologyInverseImage q) (openCohomologyInverseImage (q ≫ p))
    (abelianPullbackCompIso p q).symm
    (openFreeAbelianFunctor X) (openFreeAbelianFunctor Y) (openFreeAbelianFunctor Z)
    (Opens.map p) (Opens.map q)
    (openFreeAbelianPullbackIso p) (openFreeAbelianPullbackIso q)
    (openFreeAbelianPullbackIso (q ≫ p))
    (fun U => (openFreeAbelianPullbackIso_comp_inv p q U).symm) a b n U

end TopCat.Sheaf
