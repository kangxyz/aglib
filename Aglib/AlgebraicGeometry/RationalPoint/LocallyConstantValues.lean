/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Connected.JacobsonValues
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Rational-point local constancy on connected field schemes

Closed points are rational over an algebraically closed field. Local constancy
of values at actual rational sections therefore implies equality of all such
values on a preconnected locally finite-type scheme. No compactness, finite
image or cohomology theorem is a premise.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v
namespace AlgebraicGeometry.Scheme

/-- Actual rational-section values locally constant on open neighborhoods
are constant on a preconnected locally finite-type field scheme. -/
theorem eq_of_rationalPoint_local_constancy {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} [PreconnectedSpace T] (t : T ⟶ Spec (.of k))
    [LocallyOfFiniteType t] {A : Type v}
    (value : {b : Spec (.of k) ⟶ T // b ≫ t = 𝟙 _} → A)
    (hlocal : ∀ b, ∃ U : Set T, IsOpen U ∧ b.1 (IsLocalRing.closedPoint k) ∈ U ∧
      ∀ b', b'.1 (IsLocalRing.closedPoint k) ∈ U → value b' = value b)
    (b b' : {b : Spec (.of k) ⟶ T // b ≫ t = 𝟙 _}) : value b = value b' := by
  let : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace t
  apply TopologicalSpace.eq_of_closedPoint_open_neighborhoods
    (fun b : {b : Spec (.of k) ⟶ T // b ≫ t = 𝟙 _} => b.1 (IsLocalRing.closedPoint k))
    value ?_ hlocal b b'
  intro x hx
  exact ⟨⟨pointOfClosedPoint t x hx, pointOfClosedPoint_comp t x hx⟩,
    pointOfClosedPoint_apply t x hx _⟩

end AlgebraicGeometry.Scheme
