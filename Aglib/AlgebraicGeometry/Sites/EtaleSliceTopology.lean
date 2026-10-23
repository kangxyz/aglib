/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSlice
public import Mathlib.CategoryTheory.Sites.Equivalence

/-! # The original topology on an etale slice

The actual etale-slice category equivalence preserves and reflects covering
sieves. This uses the original jointly surjective covering criterion, and
therefore identifies the original sheaf categories at arbitrary value sizes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Etale

universe u v w

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Postcomposition with an etale chart preserves and reflects the original
covering sieves, since it retains every scheme and every covering point. -/
theorem postcompose_pushforward_mem_iff {V : Y.Etale} (R : Sieve V) :
    R.functorPushforward (MorphismProperty.Over.map ⊤ (show Etale f from inferInstance)) ∈
        Scheme.smallEtaleTopology X _ ↔ R ∈ Scheme.smallEtaleTopology Y V := by
  change _ ∈ X.smallGrothendieckTopology (@Etale : MorphismProperty Scheme.{u}) _ ↔
    R ∈ Y.smallGrothendieckTopology (@Etale : MorphismProperty Scheme.{u}) V
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology,
    Scheme.mem_toGrothendieck_smallPretopology]
  constructor
  · intro h x
    obtain ⟨W, a, y, ha, _, hy⟩ := h x
    obtain ⟨Z, b, c, hb, hcb⟩ := ha
    refine ⟨Z, b, c.left y, hb, inferInstance, ?_⟩
    have he := congrArg (fun g => g.left) hcb
    exact (congrArg (fun g : W.left ⟶ V.left => g y) he).symm.trans hy
  · intro h x
    obtain ⟨W, a, y, ha, he, hy⟩ := h x
    let F := MorphismProperty.Over.map ⊤ (show Etale f from inferInstance)
    exact ⟨F.obj W, F.map a, y, Sieve.image_mem_functorPushforward F R ha, he, hy⟩

variable (U : X.Etale)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual inverse slice equivalence identifies the two original topologies. -/
theorem sliceBackward_pushforward_mem_iff {V : U.left.Etale} (R : Sieve V) :
    R.functorPushforward (sliceBackward U) ∈
        (Scheme.smallEtaleTopology X).over U _ ↔
      R ∈ Scheme.smallEtaleTopology U.left V := by
  rw [GrothendieckTopology.mem_over_iff]
  change (R.functorPushforward (sliceBackward U)).functorPushforward (Over.forget U) ∈
    Scheme.smallEtaleTopology X _ ↔ _
  rw [← Sieve.functorPushforward_comp]
  exact postcompose_pushforward_mem_iff U.hom R

instance sliceBackward_isDenseSubsite : (sliceEquivalence U).inverse.IsDenseSubsite
    (Scheme.smallEtaleTopology U.left) ((Scheme.smallEtaleTopology X).over U) where
  functorPushforward_mem_iff := sliceBackward_pushforward_mem_iff U _

/-- Sheaves on the original etale slice are sheaves on the original small-etale
site of the chart, with the coefficient universe unchanged. -/
def sliceSheafEquivalence (A : Type v) [Category.{w} A] :
    Sheaf ((Scheme.smallEtaleTopology X).over U) A ≌
      Sheaf (Scheme.smallEtaleTopology U.left) A :=
  (sliceEquivalence U).sheafCongr _ _ A

end AlgebraicGeometry.Scheme.Etale
