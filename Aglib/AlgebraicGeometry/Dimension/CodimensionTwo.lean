/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Aglib.AlgebraicGeometry.Stalk.Dimension

/-!
# Surface stalk dimension and codimension-two closedness

Source: `R5Lab.Aglib.AlgebraicGeometry.Dimension.SurfaceStalks`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `58b4aff4fcd8a4abb58236152d15a3706dda34d1c171a6c8d71bdca6832f6ce9`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme
universe u

/-- The dimension bound required to truncate the general coniveau obstruction.
This is a geometric hypothesis, independent of every K-theory map. -/
def SurfaceDimensionAtMostTwo (X : Scheme.{u}) : Prop :=
  ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2

/-- The explicit closedness bridge for the all-codimension-two index.
It is not inferred from normality. -/
def CodimensionTwoPointsClosed (X : Scheme.{u}) : Prop :=
  ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 2 → IsClosed ({x} : Set X)

/-- The required closedness is proved from the dimension bound: a strict
specialization of a point of stalk dimension two would have dimension at least
three. This uses the actual scheme stalk/coheight theorem, mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612, `AlgebraicGeometry/Properties.lean:376`
(Stacks Tag 02IZ), and strict antitonicity of finite coheight. -/
theorem codimensionTwoPointsClosed_of_dimension (X : Scheme.{u})
    (hdim : SurfaceDimensionAtMostTwo X) : CodimensionTwoPointsClosed X := by
  intro x hx
  apply isClosed_of_closure_subset
  intro y hy
  apply Set.mem_singleton_iff.mpr
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have hlt : y < x := lt_iff_le_not_ge.mpr
    ⟨hyx, fun hxy => hne (Specializes.antisymm hxy hyx).eq⟩
  have hx' : Order.coheight x = 2 := by
    rw [ringKrullDim_stalk_eq_coheight] at hx
    exact WithBot.coe_injective hx
  have hy' : Order.coheight y ≤ 2 := by
    have h := hdim y
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_le_coe.mp h
  have hbad := Order.coheight_strictAnti hlt (by rw [hx']; exact WithTop.coe_lt_top _)
  exact (not_lt_of_ge hy') (hx' ▸ hbad)

/-- All actual codimension-two points, before any closedness identification. -/
abbrev CodimensionTwoPoint (X : Scheme.{u}) :=
  { x : X // ringKrullDim (X.presheaf.stalk x) = 2 }

end AlgebraicGeometry.Scheme
