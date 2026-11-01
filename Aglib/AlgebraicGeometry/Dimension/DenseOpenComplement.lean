/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.KrullDimension.ClosedSubspace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Dimension of an actual closed complement to a dense open

On a topologically Noetherian scheme, a dense open contains every component
generic point. Its actual reduced closed complement therefore lowers a finite
topological dimension bound by one. The complement is the native subscheme
of the vanishing ideal, and its inclusion retains the original range equation.

The source and ambient scheme need not be integral, connected, or nonempty.
In particular the dimension-one case applies to split finite completions of
curve covers. No reducedness or field hypothesis is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- A dense open immersion into a topologically Noetherian scheme has an actual
closed complement of dimension at most `d` when the ambient dimension is at
most `d + 1`. The actual complement equation and inclusion are produced. -/
theorem Hom.exists_closedComplement_topologicalKrullDim_le
    {U X : Scheme.{u}} [NoetherianSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      Set.range j = (Set.range i)ᶜ ∧ topologicalKrullDim Z ≤ (d : ℕ) := by
  have hgeneric : genericPoints X ⊆ j.opensRange := by
    intro η hη
    by_contra hηU
    obtain ⟨W, hηW, hdisjoint⟩ :=
      genericPoint_exists_open_disjoint η hη j.opensRange hηU
    obtain ⟨x, hxW, hxj⟩ :=
      j.denseRange.inter_open_nonempty (W : Set X) W.isOpen ⟨η, hηW⟩
    have hdisjoint' : Disjoint (j.opensRange : Set X) (W : Set X) :=
      Opens.coe_disjoint.mpr hdisjoint
    exact Set.disjoint_left.mp hdisjoint' hxj hxW
  let I := IdealSheafData.vanishingIdeal j.opensRange.compl
  have hI : Set.range I.subschemeι = (Set.range j)ᶜ :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  have hsupport : (I.support : Set X) = (Set.range j)ᶜ :=
    IdealSheafData.coe_support_vanishingIdeal _
  have havoid : Disjoint (I.support : Set X) (genericPoints X) := by
    apply Set.disjoint_left.mpr
    intro x hx hxgeneric
    exact (hsupport ▸ hx) (hgeneric hxgeneric)
  have hdimZ : topologicalKrullDim I.subscheme ≤ (d : ℕ) := by
    change topologicalKrullDim (I.support : Set X) ≤ (d : ℕ)
    exact topologicalKrullDim_closed_le_of_avoids_genericPoints
      (I.support : Set X) I.support.isClosed havoid d hdim
  refine ⟨I.subscheme, I.subschemeι, inferInstance, ?_, hdimZ⟩
  rw [hI, compl_compl]

end AlgebraicGeometry.Scheme
