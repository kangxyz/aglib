/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Surjectivity from actual lifts of geometric points

The point over an algebraic closure of the original residue field is used.
Its value is computed through the two original morphisms separately.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Actual lifting of all algebraically closed field-valued points implies
surjectivity of the original morphism, without finiteness assumptions. -/
theorem surjective_of_lifts_algClosedPoints {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (F : Type u) [Field F] [IsAlgClosed F] (r : Spec (.of F) ⟶ Y),
      ∃ a : Spec (.of F) ⟶ X, a ≫ f = r) : Surjective f := by
  constructor
  intro y
  let F := AlgebraicClosure (Y.residueField y)
  let c : Spec (.of F) ⟶ Spec (Y.residueField y) :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) F))
  let r := c ≫ Y.fromSpecResidueField y
  obtain ⟨a, ha⟩ := h F r
  have hc : c (IsLocalRing.closedPoint F) = IsLocalRing.closedPoint (Y.residueField y) :=
    Subsingleton.elim _ _
  refine ⟨a (IsLocalRing.closedPoint F), ?_⟩
  calc
    f (a (IsLocalRing.closedPoint F)) = (a ≫ f) (IsLocalRing.closedPoint F) := rfl
    _ = r (IsLocalRing.closedPoint F) := congrArg (fun m => m (IsLocalRing.closedPoint F)) ha
    _ = Y.fromSpecResidueField y (c (IsLocalRing.closedPoint F)) := rfl
    _ = y := by rw [hc]; exact Scheme.fromSpecResidueField_apply _ _

end AlgebraicGeometry.Scheme.Hom
