/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Amitsur.Modules
public import Aglib.Algebra.Homology.Amitsur.ScalarExtension
public import Aglib.Algebra.Homology.Amitsur.Reflection

/-!
# Original unit-insertion coordinates for the Amitsur complex

The canonical successor comparisons split off the original first `S` factor.
The first coface inserts `1` in that factor; every later coface is the original
preceding coface tensored with the identity of `S`. The two original degree-zero
cofaces start this recursion. These are equations of the actual native maps,
including over nonreduced base rings and for arbitrary coefficient modules.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped Simplicial TensorProduct

namespace ModuleCat.Amitsur

universe u v

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : ModuleCat.{max u v} R)

/-- The original tensor associator intertwines the original two tensor functors. -/
theorem tensorModule_scalarTensor_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    (tensorModule R M).map ((Algebra.Amitsur.scalarTensor R S).map f) ≫
        (TensorProduct.assoc R S B M).toModuleIso.hom =
      (TensorProduct.assoc R S A M).toModuleIso.hom ≫
        (scalarTensorFunctor R S).map ((tensorModule R M).map f) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro s a m
  rfl

/-- The original first coface inserts the original unit in the leading factor. -/
theorem coface_zero_successorIso (n : ℕ) :
    (cosimplicial R S M).δ (0 : Fin (n + 2)) ≫ (successorIso R S M n).hom =
      ModuleCat.ofHom (TensorProduct.mk R S ((complex R S M).X n) 1) := by
  change (tensorModule R M).map ((Algebra.Amitsur.conerve R S).δ 0) ≫
      ((tensorModule R M).map (Algebra.Amitsur.successorToTensor R S n) ≫
        (TensorProduct.assoc R S (Algebra.Amitsur.term R S n) M).toModuleIso.hom) = _
  rw [← Category.assoc, ← Functor.map_comp, Algebra.Amitsur.δ_zero_successorToTensor]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a m
  rfl

/-- The original second degree-zero coface inserts the unit after the first factor. -/
theorem coface_one_successorIso_zero_apply
    (a : Algebra.Amitsur.term R S 0) (m : M) :
    ((cosimplicial R S M).δ (1 : Fin 2) ≫ (successorIso R S M 0).hom)
        (a ⊗ₜ[R] m) =
      (Algebra.Amitsur.zeroTo R S).hom a ⊗ₜ[R]
        ((1 : Algebra.Amitsur.term R S 0) ⊗ₜ[R] m) := by
  change ((tensorModule R M).map ((Algebra.Amitsur.conerve R S).δ 1) ≫
    (tensorModule R M).map (Algebra.Amitsur.successorToTensor R S 0) ≫
    (TensorProduct.assoc R S (Algebra.Amitsur.term R S 0) M).toModuleIso.hom)
      (a ⊗ₜ[R] m) = _
  rw [← Functor.map_comp_assoc, Algebra.Amitsur.δ_one_successorToTensor_zero]
  rfl

/-- Every later original coface is the preceding unit insertion after the leading factor. -/
theorem coface_succ_successorIso (n : ℕ) (i : Fin (n + 2)) :
    (cosimplicial R S M).δ i.succ ≫ (successorIso R S M (n + 1)).hom =
      (successorIso R S M n).hom ≫
        (scalarTensorFunctor R S).map ((cosimplicial R S M).δ i) := by
  change (tensorModule R M).map ((Algebra.Amitsur.conerve R S).δ i.succ) ≫
      ((tensorModule R M).map (Algebra.Amitsur.successorToTensor R S (n + 1)) ≫
        (TensorProduct.assoc R S (Algebra.Amitsur.term R S (n + 1)) M).toModuleIso.hom) =
    ((tensorModule R M).map (Algebra.Amitsur.successorToTensor R S n) ≫
      (TensorProduct.assoc R S (Algebra.Amitsur.term R S n) M).toModuleIso.hom) ≫
        (scalarTensorFunctor R S).map ((cosimplicial R S M).δ i)
  rw [← Category.assoc, ← Functor.map_comp,
    Algebra.Amitsur.δ_succ_successorToTensor, Functor.map_comp, Category.assoc,
    tensorModule_scalarTensor_naturality, ← Category.assoc]
  rfl

/-- The actual original differential is the alternating sum of these original unit insertions. -/
theorem augmentedComplex_d_succ (n : ℕ) :
    (augmentedComplex R S M).d (n + 1) (n + 2) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (cosimplicial R S M).δ i :=
  AlgebraicTopology.Amitsur.augmentedObj_d_succ (augmentedObject R S M) n

end ModuleCat.Amitsur
