/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationGraded
public import Aglib.AlgebraicGeometry.Modules.Rees.AffineOpenImage

/-! # Actual affine section lifts in the ordinary relation tower -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}
  {P F : AdicSystem X K} (φ : P ⟶ F)

instance relation_isQuasicoherent (n : ℕ) : (relation φ n).IsQuasicoherent :=
  quasicoherent_of_affineCharts _ (fun R j _ => (relation_coherent φ n R j).1)

instance relationGradedPiece_isQuasicoherent (n : ℕ) :
    (relationGradedPiece φ n).IsQuasicoherent := quasicoherent_kernel (relationTransition φ n)

@[reassoc (attr := simp)]
theorem relationMap_comp {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    relationMap φ h' ≫ relationMap φ h = relationMap φ (h.trans h') := by
  apply (cancel_mono (kernel.ι (φ.hom.app (op n)))).mp
  simp only [Category.assoc, relationMap_ι, relationMap_ι_assoc]
  rw [← P.obj.map_comp]
  congr 1

@[simp]
theorem relationMap_refl (n : ℕ) : relationMap φ (le_refl n) = 𝟙 (relation φ n) := by
  apply (cancel_mono (kernel.ι (φ.hom.app (op n)))).mp
  simp [relationMap]

/-- Every original relation reduction is surjective on an affine open.
Quasicoherence of its ordinary kernel, not cartesian compatibility, is used. -/
theorem relationMap_app_surjective {n m : ℕ} (h : n ≤ m)
    [Epi (φ.hom.app (op m))] (U : X.affineOpens) :
    Function.Surjective ((relationMap φ h).app U.1) := by
  have : Epi (relationMap φ h) := relationMap_epi φ h
  let : (kernel (relationMap φ h)).IsQuasicoherent := quasicoherent_kernel (relationMap φ h)
  exact affineOpenSections_epi_surjective U (relationMap φ h)

/-- An original successive relation section lifts to every higher finite
level and lies in the kernel of reduction to its lower graded level. -/
theorem exists_relationGradedPiece_section_lift {n m : ℕ} (h : n + 1 ≤ m)
    [Epi (φ.hom.app (op m))] (U : X.affineOpens)
    (y : Γ(relationGradedPiece φ n, U.1)) :
    ∃ x : Γ(relation φ m, U.1),
      (relationMap φ h).app U.1 x = (kernel.ι (relationTransition φ n)).app U.1 y ∧
      (relationMap φ ((Nat.le_succ n).trans h)).app U.1 x = 0 := by
  obtain ⟨x, hx⟩ := relationMap_app_surjective φ h U
    ((kernel.ι (relationTransition φ n)).app U.1 y)
  refine ⟨x, hx, ?_⟩
  have hc := congrArg (fun k => k.app U.1 x) (relationMap_comp φ (Nat.le_succ n) h)
  change (relationTransition φ n).app U.1 ((relationMap φ h).app U.1 x) = _ at hc
  rw [hx] at hc
  have hz := congrArg (fun k => k.app U.1 y) (kernel.condition (relationTransition φ n))
  exact hc.symm.trans hz

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
