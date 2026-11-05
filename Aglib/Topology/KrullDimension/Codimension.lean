/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Data.Nat.Cast.Order.Basic

/-! # Dimension drop from a uniform codimension bound

A continuous injection between sober spaces preserves strict specialization
chains. If every image point has coheight at least `c`, appending an ambient
chain of length `c` lowers the dimension bound by `c`. No irreducibility,
Noetherianity, closedness of the image, or catenarity is required.
-/

@[expose] public noncomputable section

open Order TopologicalSpace Topology

attribute [local instance] specializationOrder

namespace TopologicalSpace

/-- A continuous injection whose image has codimension at least `c` lowers
an ambient dimension bound `d + c` to `d`. Codimension means coheight in the
actual specialization order, not dimension of the source local rings. -/
theorem topologicalKrullDim_le_of_coheight_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [T0Space X] [QuasiSober Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f)
    (d c : ℕ) (hcodim : ∀ x : X, (c : ℕ∞) ≤ Order.coheight (f x))
    (hdim : topologicalKrullDim Y ≤ (d + c : ℕ)) :
    topologicalKrullDim X ≤ (d : ℕ) := by
  rw [topologicalKrullDim, krullDim_eq_of_orderIso
    (irreducibleSetEquivPoints (α := X))]
  have hY : krullDim Y ≤ (d + c : ℕ) := by
    rw [← krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))]
    exact hdim
  refine iSup_le fun p => ?_
  let q := p.map f (hf.specialization_monotone.strictMono_of_injective hinj)
  obtain ⟨r, hr, hlen⟩ := exists_series_of_le_coheight (f p.last) (hcodim p.last)
  have hqr : q.last = r.head := by exact hr.symm
  have hlength := (LTSeries.length_le_krullDim (q.smash r hqr)).trans hY
  have hlength' : p.length + c ≤ d + c := by
    simpa only [RelSeries.smash_length, q, LTSeries.map_length, hlen, Nat.cast_le]
      using hlength
  exact Nat.cast_le.mpr (Nat.le_of_add_le_add_right hlength')

end TopologicalSpace
