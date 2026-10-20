/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.H2.Continuous.CupBilinear
public import Aglib.GroupCohomology.Continuous.Corestriction.ProjectionFormula
public import Aglib.GroupCohomology.Continuous.Corestriction.Tower
public import Aglib.GroupCohomology.H1.Continuous.Transgression.FiniteNaturality

/-! Consumer computations on the actual native continuous H1/H2 quotient carriers. -/

@[expose] public section

open GroupCohomology

variable (G A : Type*) [_root_.Group G] [Subsingleton G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- Every native continuous H1 class on a singleton group vanishes. -/
example (q : ContinuousH1.H1 G A) : q = 0 := by
  obtain ⟨c, rfl⟩ := ContinuousH1.classOf_surjective G A q
  have hc : c = 0 := by
    apply ContinuousH1.Cocycle.ext
    intro g
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    exact c.map_one
  rw [hc, map_zero]

/-- Unnormalized continuous two-cocycles on a singleton group are actual bar boundaries. -/
example (q : H2.Continuous.Group G A) : q = 0 := by
  obtain ⟨z, rfl⟩ := H2.Continuous.classOf_surjective G A q
  let a : C(G, A) := ContinuousMap.const G (z.val (1, 1))
  have hz : H2.Continuous.d₁ G A a = z := by
    apply H2.Continuous.Cocycle.ext
    intro g h
    have hg : g = 1 := Subsingleton.elim _ _
    have hh : h = 1 := Subsingleton.elim _ _
    subst g
    subst h
    rw [H2.Continuous.d₁_apply]
    simp [a]
  rw [← hz, H2.Continuous.classOf_d₁]
