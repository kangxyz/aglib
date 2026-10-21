/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Unit coordinates of an original tensor presentation -/

@[expose] public noncomputable section

universe u
open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

variable {B R : Type u} [CommRing B] [CommRing R] [Algebra B R]
  {L : ModuleCat.{u} B} {M N : ModuleCat.{u} R}

/-- The original quotient image of an inverse coordinate unit. -/
def algebraTensorPresentationUnitEquation
    (e : M ≅ ModuleCat.of R (R ⊗[B] L)) (q : M ⟶ N) (m : L) (z : N) : Prop :=
  q (e.inv ((1 : R) ⊗ₜ[B] m)) = z

/-- Cancel the original coordinate isomorphism before specializing the
presentation. The factorization and unit image are explicit original equations. -/
theorem algebraTensorPresentationUnitEquation_of_factorization
    (e : M ≅ ModuleCat.of R (R ⊗[B] L)) (q : M ⟶ N)
    (p : ModuleCat.of R (R ⊗[B] L) ⟶ N) (hq : q = e.hom ≫ p)
    (m : L) (z : N) (hp : p ((1 : R) ⊗ₜ[B] m) = z) :
    algebraTensorPresentationUnitEquation e q m z := by
  unfold algebraTensorPresentationUnitEquation
  rw [hq, comp_apply]
  have he := congrArg (fun k => k ((1 : R) ⊗ₜ[B] m)) e.inv_hom_id
  exact (congrArg p he).trans hp

end ModuleCat
