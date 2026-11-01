/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.FiniteProducts
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Relative dimension of the original finite products

The existing native finite product over a base adds smooth relative
dimensions. Its empty product remains
the original base. The ordered effective-divisor parameter schemes consume
these statements without introducing another product realization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

-- Match the native over-product and pullback structure-map presentations.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Smooth relative dimensions add for the original binary product over
the base. -/
theorem smoothOfRelativeDimension_overProd (X Y : Over S) (m n : ℕ)
    [SmoothOfRelativeDimension m X.hom] [SmoothOfRelativeDimension n Y.hom] :
    SmoothOfRelativeDimension (m + n) (X ⨯ Y).hom := by
  rw [overProd_hom_eq]
  have : SmoothOfRelativeDimension n (pullback.fst X.hom Y.hom) :=
    MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ inferInstance
  have : SmoothOfRelativeDimension (n + m) (pullback.fst X.hom Y.hom ≫ X.hom) :=
    smoothOfRelativeDimension_comp n m _ _
  simpa only [Nat.zero_add, Nat.add_zero, Nat.add_comm] using
    (smoothOfRelativeDimension_comp 0 (n + m)
      (Over.prodLeftIsoPullback X Y).hom (pullback.fst X.hom Y.hom ≫ X.hom))

-- The zero case uses the definitionally identical native identity over the base.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The relative dimension of the existing finite native product is the
sum of the given relative dimensions. -/
theorem smoothOfRelativeDimension_finiteProductOver {n : ℕ}
    (X : Fin n → Over S) (d : Fin n → ℕ)
    [∀ i, SmoothOfRelativeDimension (d i) (X i).hom] :
    SmoothOfRelativeDimension (∑ i, d i) (finiteProductOver X).hom := by
  induction n with
  | zero =>
    simp only [Fin.sum_univ_zero, finiteProductOver_zero, Over.mk_hom]
    exact MorphismProperty.id_mem (@SmoothOfRelativeDimension.{u} 0) S
  | succ n ih =>
    have : SmoothOfRelativeDimension (∑ i : Fin n, d i.succ)
        (finiteProductOver (fun i : Fin n => X i.succ)).hom := ih _ _
    rw [Fin.sum_univ_succ, finiteProductOver_succ]
    exact smoothOfRelativeDimension_overProd _ _ _ _

end AlgebraicGeometry.Scheme
