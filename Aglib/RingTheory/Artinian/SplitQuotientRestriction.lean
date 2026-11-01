/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Artinian.SplitReductionFieldStage

/-! # Restricting an original split quotient to its coefficient ring

The actual characters of a tensor-product quotient restrict through an
injective coefficient map when their values lie in its range. Their original
tensor universal property constructs the restricted quotient and the whole
map square. Actual lifted coordinate preimages give surjectivity. Nilpotence
of the kernel is reflected only when the original source module is flat;
no injection after arbitrary nonflat tensoring is asserted.
-/

@[expose] public noncomputable section

open scoped TensorProduct BigOperators

namespace Algebra.FiniteAlgebra

universe u v w x y

variable {R : Type u} [CommRing R]
  {C : Type v} [CommRing C] [Algebra R C]
  {L : Type w} [CommRing L] [Algebra R L]
  {A : Type x} [CommRing A] [Algebra R A]
  {J : Type y}

/-- Restrict the original quotient characters through the actual coefficient
embedding, then use the original tensor-product universal property. -/
def splitQuotientRestriction (i : C →ₐ[R] L) (hi : Function.Injective i)
    (q : L ⊗[R] A →ₐ[L] (J → L))
    (hchar : ∀ a j, q (1 ⊗ₜ[R] a) j ∈ i.range) :
    C ⊗[R] A →ₐ[C] (J → C) :=
  AlgHom.liftEquiv R C A (J → C) (AlgHom.pi fun j =>
    (AlgEquiv.ofInjective i hi).symm.toAlgHom.comp
      (((((Pi.evalAlgHom L (fun _ : J => L) j).comp q).restrictScalars R).comp
        Algebra.TensorProduct.includeRight).codRestrict i.range (fun a => hchar a j)))

/-- The literal coefficient equation on a pure tensor. -/
theorem splitQuotientRestriction_tmul (i : C →ₐ[R] L) (hi : Function.Injective i)
    (q : L ⊗[R] A →ₐ[L] (J → L))
    (hchar : ∀ a j, q (1 ⊗ₜ[R] a) j ∈ i.range) (c : C) (a : A) (j : J) :
    i (splitQuotientRestriction i hi q hchar (c ⊗ₜ[R] a) j) =
      i c * q (1 ⊗ₜ[R] a) j := by
  change i (c * (AlgEquiv.ofInjective i hi).symm
    ⟨q (1 ⊗ₜ[R] a) j, hchar a j⟩) = _
  rw [map_mul]
  congr 1
  exact congrArg Subtype.val ((AlgEquiv.ofInjective i hi).apply_symm_apply
    ⟨q (1 ⊗ₜ[R] a) j, hchar a j⟩)

/-- The restricted quotient uses exactly the original base-change map. -/
theorem splitQuotientRestriction_commutes (i : C →ₐ[R] L) (hi : Function.Injective i)
    (q : L ⊗[R] A →ₐ[L] (J → L))
    (hchar : ∀ a j, q (1 ⊗ₜ[R] a) j ∈ i.range) (z : C ⊗[R] A) (j : J) :
    i (splitQuotientRestriction i hi q hchar z j) =
      q (Algebra.TensorProduct.map i (AlgHom.id R A) z) j := by
  induction z using TensorProduct.inductionOn with
  | tmul c a =>
    rw [splitQuotientRestriction_tmul]
    change i c * q (1 ⊗ₜ[R] a) j = q (i c ⊗ₜ[R] a) j
    calc
      _ = q (i c • (1 ⊗ₜ[R] a)) j := by rw [map_smul]; rfl
      _ = _ := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add z z' hz hz' => simp [hz, hz']

/-- Actual lifted preimages of the coordinate vectors make the restricted
quotient surjective, including the empty-coordinate case. -/
theorem splitQuotientRestriction_surjective [Finite J] [DecidableEq J]
    (i : C →ₐ[R] L) (hi : Function.Injective i)
    (q : L ⊗[R] A →ₐ[L] (J → L))
    (hchar : ∀ a j, q (1 ⊗ₜ[R] a) j ∈ i.range)
    (p : J → C ⊗[R] A)
    (hp : ∀ j, q (Algebra.TensorProduct.map i (AlgHom.id R A) (p j)) = Pi.single j 1) :
    Function.Surjective (splitQuotientRestriction i hi q hchar) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  have hpre (j : J) : splitQuotientRestriction i hi q hchar (p j) = Pi.single j 1 := by
    funext j'
    apply hi
    rw [splitQuotientRestriction_commutes, hp]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  intro y
  refine ⟨∑ j, y j • p j, ?_⟩
  simp only [map_sum, map_smul, hpre]
  ext j
  simp [Pi.single_apply]

/-- Kernel-power nilpotence descends along the actual coefficient injection
only after flatness of the original source algebra has been supplied. -/
theorem splitQuotientRestriction_ker_pow [Module.Flat R A]
    (i : C →ₐ[R] L) (hi : Function.Injective i)
    (q : L ⊗[R] A →ₐ[L] (J → L))
    (hchar : ∀ a j, q (1 ⊗ₜ[R] a) j ∈ i.range)
    (n : ℕ) (hn : (RingHom.ker q.toRingHom) ^ n = ⊥) :
    (RingHom.ker (splitQuotientRestriction i hi q hchar).toRingHom) ^ n = ⊥ := by
  let f := Algebra.TensorProduct.map i (AlgHom.id R A)
  let g : (J → C) →+* (J → L) :=
    RingHom.pi fun j => i.toRingHom.comp (Pi.evalRingHom (fun _ : J => C) j)
  have hf : Function.Injective f :=
    Module.Flat.rTensor_preserves_injective_linearMap i.toLinearMap hi
  have hsquare (z : C ⊗[R] A) : q (f z) = g (splitQuotientRestriction i hi q hchar z) := by
    funext j
    exact (splitQuotientRestriction_commutes i hi q hchar z j).symm
  exact RingHom.ker_pow_eq_bot_of_injective_square f
    (splitQuotientRestriction i hi q hchar).toRingHom q.toRingHom g hf hsquare n hn

end Algebra.FiniteAlgebra
