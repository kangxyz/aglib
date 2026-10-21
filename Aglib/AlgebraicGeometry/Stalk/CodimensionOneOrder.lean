/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Order and closedness of actual codimension-one points

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.CodimensionOneClosed`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `07a5f6bee91d44a32850439247f28d187023eaec80754a30a8a2ffd62a030e1f`, selected lines [[17,
37]].
Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.CodimensionOneSpecialization`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `bb72f320e8115e9b1427284b1c66e1900b94b15b4ebe4c7e8f208e311a50cc99`, selected lines [[14,
31]].
Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.GenericPoint`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `ed6729ebbc28b88f33a66634ddd107ec33860ec8c457cf33dbf1c86e496e99e1`, selected lines [[18,
22]].
The actual scheme objects, canonical maps, universes and conditions are retained.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme

/-- The actual generic-point stalk of an integral scheme has dimension zero. -/
theorem genericPoint_stalk_dimension_zero (X : Scheme.{u}) [IsIntegral X] :
    ringKrullDim (X.presheaf.stalk (genericPoint X)) = 0 := by
  change ringKrullDim X.functionField = 0
  exact ringKrullDim_eq_zero_of_field _

namespace CodimensionOnePoint

/-- A codimension-one point is closed if every actual stalk has dimension at most one. -/
theorem isClosed_singleton_of_stalk_dimension_le_one {X : Scheme.{u}}
    (hbound : ∀ z : X, ringKrullDim (X.presheaf.stalk z) ≤ 1)
    (d : CodimensionOnePoint X) : IsClosed ({d.1} : Set X) := by
  apply isClosed_of_closure_subset
  intro y hy
  apply Set.mem_singleton_iff.mpr
  have hyd : y ≤ d.1 := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have hlt : y < d.1 := lt_iff_le_not_ge.mpr
    ⟨hyd, fun hdy => hne (Specializes.antisymm hdy hyd).eq⟩
  have hd : Order.coheight d.1 = 1 := by
    have h := d.2
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_injective h
  have hy' : Order.coheight y ≤ 1 := by
    have h := hbound y
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_le_coe.mp h
  have hbad := Order.coheight_strictAnti hlt (by rw [hd]; exact WithTop.coe_lt_top _)
  exact (not_lt_of_ge hy') (hd ▸ hbad)

/-- Two actual codimension-one points that specialize to each other are equal. -/
theorem eq_of_specializes {X : Scheme.{u}} (x y : CodimensionOnePoint X)
    (h : x.1 ⤳ y.1) : x = y := by
  apply Subtype.ext
  by_contra hn
  have hlt : y.1 < x.1 := lt_iff_le_not_ge.mpr
    ⟨h, fun hh => hn (Specializes.antisymm h hh).eq⟩
  have hx : Order.coheight x.1 = 1 := by
    have hx := x.2
    rw [ringKrullDim_stalk_eq_coheight] at hx
    exact WithBot.coe_injective hx
  have hy : Order.coheight y.1 = 1 := by
    have hy := y.2
    rw [ringKrullDim_stalk_eq_coheight] at hy
    exact WithBot.coe_injective hy
  have hb := Order.coheight_strictAnti hlt (by rw [hx]; exact WithTop.coe_lt_top _)
  rw [hx, hy] at hb
  exact lt_irrefl _ hb

end CodimensionOnePoint
end AlgebraicGeometry.Scheme
