/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceCategory
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Topology of the actual small étale slice -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {X S : Scheme.{u}}

/-- Chart postcomposition reflects covering sieves as well as preserving them. -/
theorem siteEtalePostcompose_cover_iff (f : S ⟶ X) [Etale f]
    {U : S.Etale} (R : Sieve U) :
    R.functorPushforward (siteEtalePostcompose f) ∈
      Scheme.smallEtaleTopology X ((siteEtalePostcompose f).obj U) ↔
      R ∈ Scheme.smallEtaleTopology S U := by
  refine ⟨?_, (siteEtalePostcompose_coverPreserving f).cover_preserve⟩
  intro hR
  change _ ∈ X.smallGrothendieckTopology @Etale _ at hR
  change R ∈ S.smallGrothendieckTopology @Etale U
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology] at hR ⊢
  intro x
  obtain ⟨V, a, y, ha, _, hax⟩ := hR x
  obtain ⟨W, b, c, hb, hbc⟩ := ha
  refine ⟨W, b, c.left y, hb, inferInstance, ?_⟩
  have hy : a.left y = b.left (c.left y) :=
    congrArg (fun k : V ⟶ (siteEtalePostcompose f).obj U => k.left y) hbc
  exact hy.symm.trans hax

variable (U : X.Etale)

instance etaleSliceBackward_isEquivalence : (etaleSliceBackward U).IsEquivalence :=
  inferInstanceAs (etaleSliceEquivalence U).inverse.IsEquivalence

/-- The categorical slice equivalence identifies the actual small étale topologies. -/
instance etaleSliceBackward_isDenseSubsite :
    (etaleSliceBackward U).IsDenseSubsite (Scheme.smallEtaleTopology U.left)
      ((Scheme.smallEtaleTopology X).over U) where
  functorPushforward_mem_iff {V} {R} := by
    rw [GrothendieckTopology.mem_over_iff]
    change (R.functorPushforward (etaleSliceBackward U)).functorPushforward
        (Over.forget U) ∈ Scheme.smallEtaleTopology X _ ↔ _
    rw [← Sieve.functorPushforward_comp]
    exact siteEtalePostcompose_cover_iff U.hom R

end AlgebraicGeometry.Scheme.EtaleCohomology
