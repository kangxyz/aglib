/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationScalarLifts

/-! # Positive homogeneous relation products lift into the original ideal multiple -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)

omit [IsLocallyNoetherian X] in
/-- Positive-degree original scalars act into the actual affine ideal multiple. -/
theorem positive_globalScalar_mem_ideal_smul (M : X.Modules) {r : ℕ} (hr : 0 < r)
    (a : ↥(I ^ r)) (U : X.affineOpens) (x : Γ(M, U.1)) :
    (globalScalarEndomorphism X M (idealThickeningBaseScalar f a)).app U.1 x ∈
      (idealThickeningIdealSheaf f I).ideal U •
        (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
  change ((globalScalarEndomorphism X M (idealThickeningBaseScalar f a)).val.app
    (op U.1)).hom x ∈ (idealThickeningIdealSheaf f I).ideal U •
      (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))
  rw [globalScalarEndomorphism_app]
  apply Submodule.smul_mem_smul _ (Submodule.mem_top)
  rw [idealThickeningIdealSheaf_ideal]
  exact Ideal.mem_map_of_mem _ (Ideal.pow_le_self (Nat.ne_of_gt hr) a.property)

variable {P F : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : P ⟶ F)

/-- Every positive homogeneous relation product has an original higher-level
lift in the ideal multiple and in the required reduction kernel. No cartesian
relation-kernel hypothesis or chosen lifting assumption is used. -/
theorem exists_positive_relation_section_lift (r n m : ℕ) (hr : 0 < r)
    (h : r + n + 1 ≤ m) [Epi (φ.hom.app (op m))]
    (a : ↥(I ^ r)) (U : X.affineOpens) (y : Γ(relationGradedPiece φ n, U.1)) :
    ∃ z : Γ(relation φ m, U.1),
      z ∈ (idealThickeningIdealSheaf f I).ideal U •
        (⊤ : Submodule Γ(X, U.1) Γ(relation φ m, U.1)) ∧
      (relationMap φ ((Nat.le_succ (r + n)).trans h)).app U.1 z = 0 ∧
      (relationMap φ h).app U.1 z =
        (kernel.ι (relationTransition φ (r + n))).app U.1
          ((relationGradedScalarMap f I φ r n a).app U.1 y) := by
  obtain ⟨x, hx⟩ := exists_relationGradedScalar_section_lift f I φ r n m h a U y
  let z := (globalScalarEndomorphism X (relation φ m)
    (idealThickeningBaseScalar f a)).app U.1 x
  refine ⟨z, positive_globalScalar_mem_ideal_smul f I _ hr a U x, ?_, hx⟩
  have hc := congrArg (fun k => k.app U.1 z)
    (relationMap_comp φ (Nat.le_succ (r + n)) h)
  change (relationTransition φ (r + n)).app U.1 ((relationMap φ h).app U.1 z) = _ at hc
  rw [hx] at hc
  have hz := congrArg (fun k => k.app U.1
    ((relationGradedScalarMap f I φ r n a).app U.1 y))
    (kernel.condition (relationTransition φ (r + n)))
  exact hc.symm.trans hz

end AlgebraicGeometry.Scheme.Cohomology
