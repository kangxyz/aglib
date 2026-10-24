/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisSubgroupRelative
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisSubgroupRank
public import Mathlib.GroupTheory.Sylow

/-!
# Actual Sylow covers

The original cover relative to its actual Sylow-subgroup quotient is Galois
with a p-group deck group. The quotient's original structural morphism has
rank coprime to p. The subgroup need not be normal, and the quotient over the
original base is not asserted to be Galois. These conclusions use the actual
objects and maps constructed in the subgroup-quotient leaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u
variable {X : Scheme.{u}} [ConnectedSpace X]
variable (Y : Scheme.FiniteEtale X) [IsGalois Y]
variable {p : ℕ} (P : Sylow p (Aut Y))

/-- The relative deck group of the original Sylow quotient map is a p-group,
transported through the actual original-subgroup deck equivalence. -/
theorem galoisSylowRelative_isPGroup :
    IsPGroup p (Aut (galoisSubgroupRelative Y P.toSubgroup)) :=
  P.isPGroup'.of_equiv (galoisSubgroupDeckEquiv Y P.toSubgroup)

variable [Fact p.Prime]

/-- The index of the original Sylow subgroup is coprime to the prime. -/
theorem galoisSylow_index_coprime : P.toSubgroup.index.Coprime p :=
  ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr P.not_dvd_index).symm

/-- The actual quotient's original scheme morphism has rank coprime to p. -/
theorem galoisSylowQuotient_finrank_coprime (x : X) :
    ((galoisSubgroupQuotient Y P.toSubgroup).obj.hom.finrank x).Coprime p := by
  rw [galoisSubgroupQuotient_finrank]
  exact galoisSylow_index_coprime Y P

end AlgebraicGeometry.Scheme.FiniteEtale
