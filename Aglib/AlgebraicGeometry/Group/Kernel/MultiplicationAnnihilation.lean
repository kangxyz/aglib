/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Basic

/-! The original multiplication kernel is killed by its own level. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.Kernel

attribute [local instance] Over.cartesianMonoidalCategory

/-- Multiplication by `n` is the constant unit on its original kernel,
as a morphism of the whole scheme over the actual base. -/
theorem multiplication_kernel_pow_eq_one {S : Scheme.{u}}
    (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ) :
    (𝟙 (group ((𝟙 G) ^ n)).X) ^ n = 1 := by
  let q : G ⟶ G := (𝟙 G) ^ n
  let K := group q
  let i : K.X ⟶ G.X := (inclusion q).hom.hom
  have : Mono i := (square q).mono_fst_of_mono
  have hq : q.hom.hom = (𝟙 G.X) ^ n := by
    simp only [q, Grp.Hom.hom_pow, Mon.Hom.hom_pow]
    rfl
  have hi : i ≫ q.hom.hom = 1 := (square q).w
  change (𝟙 K.X) ^ n = 1
  apply (cancel_mono i).mp
  calc
    ((𝟙 K.X) ^ n) ≫ i = i ^ n := by rw [MonObj.pow_comp, Category.id_comp]
    _ = i ≫ q.hom.hom := by rw [hq, MonObj.comp_pow, Category.comp_id]
    _ = 1 := hi
    _ = 1 ≫ i := (MonObj.one_comp i).symm

end AlgebraicGeometry.Scheme.Group.Kernel
