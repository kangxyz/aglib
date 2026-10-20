/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Comaximal ideal-sheaf intersections

Source: `R5Lab.Aglib.AlgebraicGeometry.IdealSheaf.Comaximal`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `e981f4fb879fdc85f0f372952e690509a56b712f1f4f5fe4537b74d3a7c89085`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

section
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X : Scheme.{u}} (I J H : X.IdealSheafData)

/-- Disjoint actual supports make two ideal sheaves comaximal. -/
theorem sup_eq_top_of_disjoint_support (h : Disjoint I.support H.support) : I ⊔ H = ⊤ := by
  apply (support_eq_bot_iff _).mp
  rw [support_sup]
  exact disjoint_iff.mp h

/-- A closed part disjoint from the selected component does not change its
scheme-theoretic intersection with a union. The proof uses ideal multiplication
and comaximality, not the false unrestricted distributivity of ideal lattices. -/
theorem sup_inf_eq_sup_of_comaximal (h : I ⊔ H = ⊤) :
    I ⊔ (J ⊓ H) = I ⊔ J := by
  apply le_antisymm (sup_le_sup_left inf_le_left I)
  apply sup_le le_sup_left
  calc
    J = J * ⊤ := (mul_top J).symm
    _ = J * (I ⊔ H) := by rw [h]
    _ = J * I ⊔ J * H := mul_inf J I H
    _ ≤ I ⊔ (J ⊓ H) := sup_le_sup
      (fun U => Ideal.mul_le_right) (fun U => Ideal.mul_le_inf)

/-- Support disjointness is sufficient for the exact ideal identity. -/
theorem sup_inf_eq_sup_of_disjoint_support (h : Disjoint I.support H.support) :
    I ⊔ (J ⊓ H) = I ⊔ J :=
  sup_inf_eq_sup_of_comaximal I J H (sup_eq_top_of_disjoint_support I H h)

end AlgebraicGeometry.Scheme.IdealSheafData

end
