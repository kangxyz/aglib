/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedFactor
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Reduced sources factor through original immersions

Support containment for a reduced source produces an actual factorization
through a locally closed immersion. The construction uses the immersion's
canonical open neighbourhood and its original closed factor, without
identifying schemes merely from equality of their underlying supports.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {Z X C : Scheme.{u}} [IsReduced Z]

/-- A reduced source whose image lies in an actual immersion factors
through that immersion. -/
def liftReducedToImmersion (i : C ⟶ X) [IsImmersion i]
    (f : Z ⟶ X) (hf : Set.range f ⊆ Set.range i) : Z ⟶ C := by
  have hU : Set.range f ⊆ Set.range i.coborderRange.ι := by
    rw [Scheme.Opens.range_ι]
    exact hf.trans subset_coborder
  let g := IsOpenImmersion.lift i.coborderRange.ι f hU
  have hg : g ≫ i.coborderRange.ι = f := IsOpenImmersion.lift_fac _ _ _
  refine liftReducedToClosed i.liftCoborder g ?_
  rintro _ ⟨z, rfl⟩
  obtain ⟨c, hc⟩ := hf ⟨z, rfl⟩
  refine ⟨c, i.coborderRange.ι.isOpenEmbedding.injective ?_⟩
  change (i.liftCoborder ≫ i.coborderRange.ι) c = (g ≫ i.coborderRange.ι) z
  rw [i.liftCoborder_ι, hg, hc]

@[reassoc (attr := simp)]
theorem liftReducedToImmersion_fac (i : C ⟶ X) [IsImmersion i]
    (f : Z ⟶ X) (hf : Set.range f ⊆ Set.range i) :
    liftReducedToImmersion i f hf ≫ i = f := by
  unfold liftReducedToImmersion
  conv_lhs => rhs; rw [← i.liftCoborder_ι]
  rw [← Category.assoc, liftReducedToClosed_fac, IsOpenImmersion.lift_fac]

end AlgebraicGeometry
