/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Unramified.Finite

/-!
# Rigidity of unramified algebra maps into a domain

Maps from an essentially finite-type formally unramified algebra to a domain
are determined by their reductions at any prime. The prime ideal need not be
nilpotent, and no Noetherian hypothesis is imposed.

Source: R5Lab/AlgebraicGeometry/FiniteEtale/UnramifiedRigidity.lean
at the private R5 2f9 source, frozen after the native-consumer refactor.
SHA256: ae7a23021c805bedf235075e127e7cff6672cfc9548527e143b377dbef735b3e
The selected statement, actual map equations and proof are preserved.
-/
@[expose] public section

noncomputable section

open scoped TensorProduct
universe u v w

namespace Algebra.FormallyUnramified

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [IsDomain B]
  [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]

/-- Maps from an essentially finite type unramified algebra to a domain are
determined by their reduction at a prime. The tensor separator supplies the
rigidity; no separation or Noetherian assumption is placed on the domain. -/
theorem eq_of_comp_mkQ_eq (Q : Ideal B) [Q.IsPrime] (f g : A →ₐ[R] B)
    (hfg : ∀ a, (Ideal.Quotient.mk Q) (f a) = (Ideal.Quotient.mk Q) (g a)) : f = g := by
  obtain ⟨t, ht, hμ⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).mp
      inferInstance
  let H : A ⊗[R] A →ₐ[R] B := Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)
  have hmod (z : A ⊗[R] A) :
      (Ideal.Quotient.mk Q) (H z) =
        (Ideal.Quotient.mk Q) (f (Algebra.TensorProduct.lmul' R z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
        simp only [H, Algebra.TensorProduct.lift_tmul,
          Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
        rw [hfg b]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hH : H t ≠ 0 := by
    intro h
    have := hmod t
    rw [h, hμ, map_zero, map_one, map_one] at this
    exact zero_ne_one this
  ext a
  have ha := congrArg H (ht a)
  have hz : (g a - f a) * H t = 0 := by
    simpa only [map_mul, map_sub, H, Algebra.TensorProduct.lift_tmul,
      map_one, one_mul, mul_one, map_zero] using ha
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hH)).symm

end Algebra.FormallyUnramified
