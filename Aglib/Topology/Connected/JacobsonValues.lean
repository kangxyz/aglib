/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.LocallyConstant.Basic

/-! # Locally constant values specified on closed points

On a Jacobson space, locally compatible indexed values covering all closed
points extend to a genuine locally constant function on the whole space.
Preconnectedness therefore makes the indexed values equal. No compactness,
finite image or topology on the value type is assumed.
-/

@[expose] public noncomputable section

universe u v w

namespace TopologicalSpace

/-- Closed points detect the compatibility and coverage needed to extend
indexed locally constant values to the whole Jacobson space. -/
theorem exists_locallyConstant_of_closedPoint_open_neighborhoods
    {T : Type u} [TopologicalSpace T] [JacobsonSpace T]
    {I : Type v} {A : Type w} (point : I → T) (value : I → A)
    (hclosed : ∀ x, IsClosed {x} → ∃ i, point i = x)
    (hlocal : ∀ i, ∃ U : Set T, IsOpen U ∧ point i ∈ U ∧
      ∀ j, point j ∈ U → value j = value i) :
    ∃ g : LocallyConstant T A, ∀ i, g (point i) = value i := by
  classical
  choose U hU hiU hvalue using hlocal
  have hcover : ∀ x : T, ∃ i, x ∈ U i := by
    intro x
    by_contra hx
    have hx' : x ∈ (⋃ i, U i)ᶜ := by
      intro hxU
      exact hx (Set.mem_iUnion.mp hxU)
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
      (show (⋃ i, U i)ᶜ.Nonempty from ⟨x, hx'⟩)
      (isOpen_iUnion hU).isClosed_compl.isLocallyClosed
    obtain ⟨i, rfl⟩ := hclosed z hzc
    exact hz (Set.mem_iUnion.mpr ⟨i, hiU i⟩)
  have hoverlap : ∀ i j, (U i ∩ U j).Nonempty → value i = value j := by
    intro i j hij
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hij
      ((hU i).inter (hU j)).isLocallyClosed
    obtain ⟨k, rfl⟩ := hclosed z hzc
    exact (hvalue i k hz.1).symm.trans (hvalue j k hz.2)
  choose c hc using hcover
  let g : T → A := fun x => value (c x)
  have hg : ∀ i x, x ∈ U i → g x = value i := by
    intro i x hx
    exact hoverlap (c x) i ⟨x, hc x, hx⟩
  have hconst : IsLocallyConstant g := (IsLocallyConstant.iff_exists_open g).mpr fun x =>
    ⟨U (c x), hU (c x), hc x, fun y hy => hg (c x) y hy⟩
  exact ⟨⟨g, hconst⟩, fun i => hg i (point i) (hiU i)⟩

/-- Locally constant indexed values covering the closed points of a
preconnected Jacobson space are all equal. -/
theorem eq_of_closedPoint_open_neighborhoods
    {T : Type u} [TopologicalSpace T] [JacobsonSpace T] [PreconnectedSpace T]
    {I : Type v} {A : Type w} (point : I → T) (value : I → A)
    (hclosed : ∀ x, IsClosed {x} → ∃ i, point i = x)
    (hlocal : ∀ i, ∃ U : Set T, IsOpen U ∧ point i ∈ U ∧
      ∀ j, point j ∈ U → value j = value i) (i j : I) : value i = value j := by
  obtain ⟨g, hg⟩ := exists_locallyConstant_of_closedPoint_open_neighborhoods
    point value hclosed hlocal
  exact (hg i).symm.trans ((g.apply_eq_of_preconnectedSpace (point i) (point j)).trans (hg j))

end TopologicalSpace
