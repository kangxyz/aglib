/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisSubgroupQuotient
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GeometricFiberRank
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index

/-!
# Native rank of the actual subgroup quotient

The original geometric fiber of a Galois cover is a free transitive set for
its actual deck group. Its subgroup orbits have cardinality equal to the
subgroup index. The explicit original quotient-fiber comparison and the
native geometric-fiber/rank comparison therefore compute the actual
quotient scheme morphism's `finrank`, without normality assumptions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u
variable {X : Scheme.{u}} [ConnectedSpace X]
variable (Y : Scheme.FiniteEtale X) [IsGalois Y] (H : Subgroup (Aut Y))

/-- The original geometric fiber of the actual quotient has cardinality
exactly the index of the original subgroup of deck transformations. -/
theorem galoisSubgroupQuotient_fiber_card {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) :
    Nat.card (Fiber s (galoisSubgroupQuotient Y H)) = H.index := by
  let : IsCancelSMul (Aut Y) ((fiberToFinite s).obj Y) := {
    left_cancel' := fun g a b h => smul_left_cancel g h
    right_cancel' := fun g h a hab =>
      evaluation_aut_injective_of_isConnected (fiberToFinite s) Y a hab }
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected (fiberToFinite s) Y
  exact (Nat.card_congr ((galoisSubgroupQuotientFiberEquiv Y H s).trans
    (MulAction.equivSubgroupOrbitsQuotientGroup (G := Aut Y) a H))).trans H.index_eq_card.symm

/-- The rank is the original scheme morphism's finite-flat rank, not merely
an abstract fiber cardinality. -/
theorem galoisSubgroupQuotient_finrank (x : X) :
    (galoisSubgroupQuotient Y H).obj.hom.finrank x = H.index :=
  (natCard_geometricFiber_eq_finrank (galoisSubgroupQuotient Y H) x).symm.trans
    (galoisSubgroupQuotient_fiber_card Y H (algebraicClosureResiduePoint X x))

end AlgebraicGeometry.Scheme.FiniteEtale
