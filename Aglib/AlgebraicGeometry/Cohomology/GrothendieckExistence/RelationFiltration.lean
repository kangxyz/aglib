/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationSections
public import Aglib.AlgebraicGeometry.Modules.KernelSections
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Aglib.LinearAlgebra.KernelFiltrationMap

/-! # The original finite relation filtration and its successive quotients -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}
  {P F : AdicSystem X K} (φ : P ⟶ F)

/-- The original reduction kernel, not an ideal-adic replacement. -/
def relationFiltration {n m : ℕ} (h : n ≤ m) (U : X.Opens) :
    Submodule Γ(X, U) Γ(relation φ m, U) := ((relationMap φ h).val.app (op U)).hom.ker

theorem relationSections_comp {n m : ℕ} (h : n + 1 ≤ m) (U : X.Opens) :
    ((relationTransition φ n).val.app (op U)).hom.comp ((relationMap φ h).val.app (op U)).hom =
      ((relationMap φ ((Nat.le_succ n).trans h)).val.app (op U)).hom :=
  congrArg (fun k => (k.val.app (op U)).hom) (relationMap_comp φ (Nat.le_succ n) h)

/-- Reduction to the adjacent original kernel is the actual successive
filtration quotient map, expressed in original sheaf sections. -/
def relationFiltrationMap {n m : ℕ} (h : n + 1 ≤ m) (U : X.Opens) :
    relationFiltration φ ((Nat.le_succ n).trans h) U →ₗ[Γ(X, U)]
      Γ(relationGradedPiece φ n, U) :=
  (kernelSectionsLinearEquiv (relationTransition φ n) U).symm.toLinearMap.comp
    (LinearMap.kernelFiltrationMap ((relationMap φ h).val.app (op U)).hom
      ((relationTransition φ n).val.app (op U)).hom
      ((relationMap φ ((Nat.le_succ n).trans h)).val.app (op U)).hom
      (relationSections_comp φ h U))

@[simp]
theorem relationFiltrationMap_ι {n m : ℕ} (h : n + 1 ≤ m) (U : X.Opens)
    (x : relationFiltration φ ((Nat.le_succ n).trans h) U) :
    (kernel.ι (relationTransition φ n)).app U (relationFiltrationMap φ h U x) =
      (relationMap φ h).app U x := by
  rw [← kernelSectionsLinearEquiv_apply]
  dsimp only [relationFiltrationMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The kernel is precisely the next original filtration term. -/
theorem ker_relationFiltrationMap {n m : ℕ} (h : n + 1 ≤ m) (U : X.Opens) :
    (relationFiltrationMap φ h U).ker =
      (relationFiltration φ h U).comap
        (relationFiltration φ ((Nat.le_succ n).trans h) U).subtype := by
  ext x
  change relationFiltrationMap φ h U x = 0 ↔ (relationMap φ h).app U x = 0
  rw [← relationFiltrationMap_ι φ h U x]
  constructor
  · intro hx
    rw [hx, map_zero]
  · intro hx
    apply moduleHom_app_injective (kernel.ι (relationTransition φ n)) U
    simpa only [map_zero] using hx

/-- Surjectivity uses original surjective relation reductions, not any
cartesian property of the ordinary kernel tower. -/
theorem relationFiltrationMap_surjective {n m : ℕ} (h : n + 1 ≤ m)
    [Epi (φ.hom.app (op m))] (U : X.affineOpens) :
    Function.Surjective (relationFiltrationMap φ h U.1) :=
  (kernelSectionsLinearEquiv (relationTransition φ n) U.1).symm.surjective.comp
    (LinearMap.kernelFiltrationMap_surjective _ _ _ _
      (relationMap_app_surjective φ h U))

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
