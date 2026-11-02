/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Pullback.DenseRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # The original coefficient unit on a surjective etale cover

Restriction is faithful because the original postcomposition functor is
cover dense. This is only faithfulness, not fullness: distinct structure maps
to the covering scheme need not agree locally. The original inverse-image
adjunction unit is therefore a monomorphism for every abelian coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : S ⟶ X) [Etale f] [Surjective f]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Postcomposition by a surjective etale chart is cover dense on the actual
small-etale site. No local fullness statement is asserted. -/
instance siteEtalePostcompose_isCoverDense :
    (siteEtalePostcompose f).IsCoverDense (Scheme.smallEtaleTopology X) where
  is_cover U := by
    change _ ∈ X.smallGrothendieckTopology (@Etale : MorphismProperty Scheme.{u}) U
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
      Scheme.mem_toGrothendieck_smallPretopology]
    intro x
    let V := (siteBaseChange f).obj U
    let a := (siteEtalePostcomposeAdj f).counit.app U
    obtain ⟨y, hy⟩ := (show Surjective (pullback.fst U.hom f) from inferInstance).surj x
    exact ⟨(siteEtalePostcompose f).obj V, a, y,
      Presieve.in_coverByImage (siteEtalePostcompose f) a, inferInstance, hy⟩

/-- Actual coefficient restriction to a surjective etale chart is faithful. -/
instance etaleRestriction_faithful : (etaleRestriction f).Faithful :=
  CategoryTheory.Functor.sheafPushforwardContinuous_faithful_of_isCoverDense.{
    u + 1, u, u + 1, u, u + 1}
    (siteEtalePostcompose f) (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X)

/-- The original inverse image on a surjective etale cover is faithful. -/
instance inverseImage_faithful : (inverseImage f).Faithful :=
  Functor.Faithful.of_iso (inverseImageEtaleIso f).symm

/-- The actual inverse-image/direct-image unit embeds every original
coefficient sheaf. -/
instance inverseImageAdjunction_unit_mono (F : AbelianSheaf.{u, u + 1} X) :
    Mono ((inverseImageAdjunction f).unit.app F) :=
  Adjunction.unit_mono_of_L_faithful (inverseImageAdjunction f) F

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
