/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.KrullDimension.Codimension
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Actual closed complements from local codimension bounds

An open containing all points of local dimension below `c` has an actual
closed complement with dimension at most `d` when the ambient scheme has
dimension at most `d + c`. The closed scheme is the native vanishing-ideal
subscheme, with its original inclusion and complement equation. No
Noetherianity, normality, irreducibility, or field hypothesis is imposed.

For `c = 2` this is the dimension conversion required by the sharp proper
cohomological bound. Extension of a normal rational map across codimension-one
points is a separate geometric premise, not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- A lower bound on the dimensions of ambient local rings outside an open
produces its actual closed complement and the corresponding dimension drop. -/
theorem Hom.exists_closedComplement_topologicalKrullDim_le_of_codimension
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (d c : ℕ) (hdim : topologicalKrullDim X ≤ (d + c : ℕ))
    (hcodim : ∀ x : X, x ∉ Set.range j →
      (c : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      Set.range j = (Set.range i)ᶜ ∧ topologicalKrullDim Z ≤ (d : ℕ) := by
  let I := IdealSheafData.vanishingIdeal j.opensRange.compl
  have hI : Set.range I.subschemeι = (Set.range j)ᶜ :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  have hdimZ : topologicalKrullDim I.subscheme ≤ (d : ℕ) := by
    apply topologicalKrullDim_le_of_coheight_image I.subschemeι
      I.subschemeι.continuous I.subschemeι.isClosedEmbedding.injective d c ?_ hdim
    intro z
    have hz : I.subschemeι z ∉ Set.range j := by
      rw [← Set.mem_compl_iff, ← hI]
      exact Set.mem_range_self z
    have h := hcodim (I.subschemeι z) hz
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_le_coe.mp h
  refine ⟨I.subscheme, I.subschemeι, inferInstance, ?_, hdimZ⟩
  rw [hI, compl_compl]

end AlgebraicGeometry.Scheme
