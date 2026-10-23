/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Pullback

/-!
# Surjective base change reflects original etale covers

This is a statement about the actual small-etale covering sieves and their
actual base-change functor. It makes no cohomological base-change assertion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Surjective scheme base change preserves and reflects original covering sieves. -/
theorem siteBaseChange_pushforward_mem_iff {X S : Scheme.{u}}
    (f : S ⟶ X) [Surjective f] {U : X.Etale} (R : Sieve U) :
    R.functorPushforward (siteBaseChange f) ∈ S.smallEtaleTopology _ ↔
      R ∈ X.smallEtaleTopology U := by
  constructor
  · intro h
    change _ ∈ S.smallGrothendieckTopology @Etale _ at h
    change R ∈ X.smallGrothendieckTopology @Etale U
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
      Scheme.mem_toGrothendieck_smallPretopology] at h ⊢
    intro x
    obtain ⟨y, hy⟩ := (pullback.fst U.hom f).surjective x
    obtain ⟨W, a, z, ha, _, hz⟩ := h y
    obtain ⟨V, b, c, hb, hcb⟩ := ha
    refine ⟨V, b, (pullback.fst V.hom f) (c.left z), hb, inferInstance, ?_⟩
    have hbproj : ((siteBaseChange f).map b).left ≫ pullback.fst U.hom f =
        pullback.fst V.hom f ≫ b.left := by
      simp [MorphismProperty.Over.pullback]
    have he : c.left ≫ ((siteBaseChange f).map b).left = a.left :=
      congrArg (fun k => k.left) hcb.symm
    calc
      b.left ((pullback.fst V.hom f) (c.left z)) =
          (pullback.fst U.hom f) (((siteBaseChange f).map b).left (c.left z)) :=
        congrArg (fun k : ((siteBaseChange f).obj V).left ⟶ U.left => k (c.left z))
          hbproj.symm
      _ = (pullback.fst U.hom f) (a.left z) :=
        congrArg (pullback.fst U.hom f) (congrArg (fun k : W.left ⟶ _ => k z) he)
      _ = (pullback.fst U.hom f) y := congrArg (pullback.fst U.hom f) hz
      _ = x := hy
  · exact (siteBaseChange_coverPreserving f).cover_preserve

end AlgebraicGeometry.Scheme.EtaleCohomology
