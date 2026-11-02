/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Coalgebra.Graded.DegreeOne
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.List.FinRange

/-!
# The degree-one dimension bound for a connected graded coalgebra

Distinct primitive degree-one basis elements have nonzero ordered product.
Consequently, if the grading vanishes above degree `g`, its finite
degree-one piece has dimension at most `g`. This uses the original native
coproduct and its signed multiplicativity, and works over every field.

The primitive hypothesis is a structural input at this leaf. Its supplier
from the grading and the two counit identities is separate; no geometric
cohomology instance or Borel--Hopf splitting is assumed here.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace GradedAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [Coalgebra R A]
  (hε : ∀ a, GradedAlgebra.proj 𝒜 0 a = Coalgebra.counit (R := R) a • (1 : A))
  (h_one : Coalgebra.comul (R := R) (1 : A) = (1 : A) ⊗ₜ[R] (1 : A))
  (h_mul : ∀ a b : A,
    GradedTensorProduct.of R 𝒜 𝒜 (Coalgebra.comul (a * b)) =
      GradedTensorProduct.of R 𝒜 𝒜 (Coalgebra.comul a) *
        GradedTensorProduct.of R 𝒜 𝒜 (Coalgebra.comul b))

include hε h_one h_mul

/-- A degree-one contraction kills a product of primitive elements on
each of which its functional vanishes. -/
theorem contraction_list_prod_eq_zero {ι : Type*} (v : ι → 𝒜 1)
    (hv : ∀ i, Coalgebra.IsSkewPrimitiveElem R (1 : A) 1 (v i : A))
    (f : Module.Dual R (𝒜 1)) (l : List ι) (hf : ∀ i ∈ l, f (v i) = 0) :
    contraction 𝒜 f (l.map (fun i => (v i : A))).prod = 0 := by
  induction l with
  | nil => simpa using contraction_one 𝒜 h_one f
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons,
        contraction_primitive_mul 𝒜 hε h_mul f (v i) (hv i),
        hf i List.mem_cons_self, zero_smul,
        ih (fun j hj => hf j (List.mem_cons_of_mem i hj)), mul_zero, sub_self]

/-- Every ordered product of distinct primitive degree-one basis
elements is nonzero. The argument needs no factorial inverse. -/
theorem basis_list_prod_ne_zero [Nontrivial A] {ι : Type*}
    (b : Module.Basis ι R (𝒜 1))
    (hb : ∀ i, Coalgebra.IsSkewPrimitiveElem R (1 : A) 1 (b i : A))
    (l : List ι) (hl : l.Nodup) :
    (l.map (fun i => (b i : A))).prod ≠ 0 := by
  classical
  induction l with
  | nil => simp
  | cons i l ih =>
      obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
      have hz : contraction 𝒜 (b.coord i) (l.map (fun j => (b j : A))).prod = 0 := by
        apply contraction_list_prod_eq_zero 𝒜 hε h_one h_mul b hb
        intro j hj
        have hji : j ≠ i := by
          intro h
          exact hi (h ▸ hj)
        simp [Module.Basis.coord_apply, hji]
      have hd : contraction 𝒜 (b.coord i)
          ((i :: l).map (fun j => (b j : A))).prod =
            (l.map (fun j => (b j : A))).prod := by
        rw [List.map_cons, List.prod_cons,
          contraction_primitive_mul 𝒜 hε h_mul (b.coord i) (b i) (hb i), hz]
        simp
      intro h
      apply ih hl
      rw [h, map_zero] at hd
      exact hd.symm

end GradedAlgebra

namespace GradedAlgebra

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] [Nontrivial A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] [Coalgebra k A]

/-- Vanishing above degree `g` bounds the dimension of a finite
primitive degree-one piece of a connected graded coalgebra. -/
theorem finrank_degreeOne_le_of_vanishing [Module.Finite k (𝒜 1)]
    (hε : ∀ a, GradedAlgebra.proj 𝒜 0 a = Coalgebra.counit (R := k) a • (1 : A))
    (h_one : Coalgebra.comul (R := k) (1 : A) = (1 : A) ⊗ₜ[k] (1 : A))
    (h_mul : ∀ a b : A,
      GradedTensorProduct.of k 𝒜 𝒜 (Coalgebra.comul (a * b)) =
        GradedTensorProduct.of k 𝒜 𝒜 (Coalgebra.comul a) *
          GradedTensorProduct.of k 𝒜 𝒜 (Coalgebra.comul b))
    (h_primitive : ∀ x : 𝒜 1, Coalgebra.IsSkewPrimitiveElem k (1 : A) 1 (x : A))
    (g : ℕ) (hvanish : ∀ n, g < n → 𝒜 n = ⊥) :
    Module.finrank k (𝒜 1) ≤ g := by
  classical
  let b := Module.finBasis k (𝒜 1)
  let l := List.finRange (Module.finrank k (𝒜 1))
  have hn : (l.map (fun i => (b i : A))).prod ≠ 0 :=
    basis_list_prod_ne_zero 𝒜 hε h_one h_mul b (fun i => h_primitive (b i))
      l (List.nodup_finRange _)
  have hm : (l.map (fun i => (b i : A))).prod ∈ 𝒜 (Module.finrank k (𝒜 1)) := by
    simpa [l] using
      (SetLike.list_prod_map_mem_graded (A := 𝒜) l (fun _ => (1 : ℕ))
        (fun i => (b i : A)) (fun i _ => (b i).property))
  by_contra h
  rw [hvanish _ (Nat.lt_of_not_ge h), Submodule.mem_bot] at hm
  exact hn hm

end GradedAlgebra
