/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace

/-! # Finite locally constant values on rational points

The open neighborhoods first cover the entire Jacobson space: a nonempty
closed complement would have a closed point. Only after that step is
compactness used to choose finitely many values. No topology or finiteness is
assumed on the value type.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace TopologicalSpace

/-- Locally constant values indexed by points which contain every closed point
have finite image on a compact Jacobson space. The open neighborhoods need not
admit continuous sections of the indexing map. -/
theorem finite_range_of_closedPoint_open_neighborhoods
    {T : Type u} [TopologicalSpace T] [CompactSpace T] [JacobsonSpace T]
    {I : Type v} {A : Type w} (point : I → T) (value : I → A)
    (hclosed : ∀ x, IsClosed {x} → ∃ i, point i = x)
    (hlocal : ∀ i, ∃ U : Set T, IsOpen U ∧ point i ∈ U ∧
      ∀ j, point j ∈ U → value j = value i) :
    (Set.range value).Finite := by
  classical
  choose U hU hiU hvalue using hlocal
  have hcover : (Set.univ : Set T) ⊆ ⋃ i, U i := by
    intro x _
    by_contra hx
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
      (show (⋃ i, U i)ᶜ.Nonempty from ⟨x, hx⟩)
      (isOpen_iUnion hU).isClosed_compl.isLocallyClosed
    obtain ⟨i, rfl⟩ := hclosed z hzc
    exact hz (Set.mem_iUnion.mpr ⟨i, hiU i⟩)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine (s.finite_toSet.image value).subset ?_
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hj, hij⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ (point i)))
  exact ⟨j, hj, (hvalue j i hij).symm⟩

end TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ProperCurveH1Family

variable {k : Type u} [Field k] [IsAlgClosed k]
  {T : Scheme.{u}} (t : T ⟶ Spec (.of k))

/-- The original rational parameters, retaining their actual structure-map
identity. This is not a replacement for the scheme parameter space. -/
abbrev RationalParameter := {b : Spec (.of k) ⟶ T // b ≫ t = 𝟙 _}

/-- Locally constant values on the actual rational parameters of a compact
locally finite-type scheme over an algebraically closed field have finite image.
Closed points are rational by the native closed-point equivalence. -/
theorem finite_range_of_rational_local_constancy [LocallyOfFiniteType t]
    [CompactSpace T] {A : Type v} (value : RationalParameter t → A)
    (hlocal : ∀ b, ∃ U : Set T, IsOpen U ∧ b.1 (IsLocalRing.closedPoint k) ∈ U ∧
      ∀ b', b'.1 (IsLocalRing.closedPoint k) ∈ U → value b' = value b) :
    (Set.range value).Finite := by
  let : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace t
  apply TopologicalSpace.finite_range_of_closedPoint_open_neighborhoods
    (fun b : RationalParameter t => b.1 (IsLocalRing.closedPoint k)) value ?_ hlocal
  intro x hx
  exact ⟨⟨pointOfClosedPoint t x hx, pointOfClosedPoint_comp t x hx⟩,
    pointOfClosedPoint_apply t x hx _⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.ProperCurveH1Family
