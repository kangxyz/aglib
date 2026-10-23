/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.ExteriorPower.BaseChange
public import Aglib.LinearAlgebra.ExteriorPower.TopDegree
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Left wedge multiplication and the kernel of the wedge map

* `exteriorPower.wedgeLeft n m : ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M`, `x ↦ m ∧ x`, is left
  multiplication by `ι m` in the exterior algebra (`coe_wedgeLeft`, `wedgeLeft_ιMulti`). It is
  natural in `M` (`map_wedgeLeft`) and compatible with base change (`coe_toBaseChange_wedgeLeft`).
* `exteriorPower.ι_mul_ιMulti_succAbove_ne_zero`: for a basis `e` of `F` indexed by `Fin (n + 1)`
  and `x` with nonzero `m`-th coordinate `c_m`, the wedge `x ∧ e_0 ∧ ⋯ ∧ ê_m ∧ ⋯ ∧ e_n` is
  nonzero; its top coordinate is `± c_m`.
* `exteriorPower.exists_wedgeLeft_ne_zero`: if `Q` is finite projective of rank `n + 1` at every
  prime and `q ≠ 0`, then `q ∧ x ≠ 0` for some `x ∈ ⋀[A]^n Q`. Localize at a maximal ideal where
  `q` survives; there `Q` is free and the previous item applies, and the base change of exterior
  powers is surjective and compatible with `wedgeLeft`.
* `exteriorPower.mem_iff_forall_wedgeLeft_mem_ker`: if `V ⧸ N` is finite projective of rank
  `n + 1` at every prime, then `v ∈ N` exactly when `v ∧ η` lies in the kernel of
  `⋀[A]^(n+1) V → ⋀[A]^(n+1) (V ⧸ N)` for every `η ∈ ⋀[A]^n V`. So a quotient of constant rank
  `n + 1` is determined by the kernel of its top exterior power.

This is the algebra behind the injectivity of the Plücker map (the Plücker coordinates separate
points; Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1, p. 9, leaves
this to the reader).
-/

@[expose] public section

noncomputable section

open TensorProduct Function

universe u v w

namespace exteriorPower

section Wedge

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

theorem ι_mul_mem (n : ℕ) (m : M) (x : ⋀[R]^n M) :
    ExteriorAlgebra.ι R m * (x : ExteriorAlgebra R M) ∈ ⋀[R]^(n + 1) M := by
  change _ ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ (n + 1)
  rw [pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) x.2

/-- Left wedge multiplication `x ↦ m ∧ x`, `⋀[R]^n M → ⋀[R]^(n + 1) M`. -/
def wedgeLeft (n : ℕ) (m : M) : ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M where
  toFun x := ⟨ExteriorAlgebra.ι R m * x, ι_mul_mem n m x⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' r _ := Subtype.ext (mul_smul_comm r _ _)

@[simp]
theorem coe_wedgeLeft (n : ℕ) (m : M) (x : ⋀[R]^n M) :
    (wedgeLeft n m x : ExteriorAlgebra R M) = ExteriorAlgebra.ι R m * x :=
  rfl

theorem wedgeLeft_ιMulti (n : ℕ) (m : M) (v : Fin n → M) :
    wedgeLeft n m (ιMulti R n v) = ιMulti R (n + 1) (Fin.cons m v) := by
  apply Subtype.ext
  have ht : Matrix.vecTail (Fin.cons m v : Fin (n + 1) → M) = v :=
    funext fun i => Fin.cons_succ (α := fun _ => M) m v i
  rw [coe_wedgeLeft, ιMulti_apply_coe, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    Fin.cons_zero, ht]

theorem wedgeLeft_zero (n : ℕ) (x : ⋀[R]^n M) : wedgeLeft n (0 : M) x = 0 :=
  Subtype.ext (by simp)

/-- Left wedge multiplication is natural in the module. -/
theorem map_wedgeLeft {N : Type w} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (n : ℕ)
    (m : M) (x : ⋀[R]^n M) : map (n + 1) f (wedgeLeft n m x) = wedgeLeft n (f m) (map n f x) := by
  apply Subtype.ext
  rw [coe_map, coe_wedgeLeft, coe_wedgeLeft, coe_map, map_mul, ExteriorAlgebra.map_apply_ι]

end Wedge

section BaseChange

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {P : Type w} [AddCommGroup P] [Module A P]

/-- The base change of exterior powers is compatible with left wedge multiplication. -/
theorem coe_toBaseChange_wedgeLeft (n : ℕ) (q : P) (x : ⋀[A]^n P) :
    (toBaseChange A B (n + 1) P (wedgeLeft n q x) : ExteriorAlgebra B (B ⊗[A] P)) =
      ExteriorAlgebra.ι B ((1 : B) ⊗ₜ[A] q) *
        (toBaseChange A B n P x : ExteriorAlgebra B (B ⊗[A] P)) := by
  have hx : x ∈ Submodule.span A (Set.range (ιMulti A n (M := P))) := by
    rw [ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [wedgeLeft_ιMulti, toBaseChange_ιMulti, toBaseChange_ιMulti, ← coe_wedgeLeft,
      wedgeLeft_ιMulti]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, mul_add, hx, hy]
  | smul a x _ hx =>
    simp only [map_smul, Submodule.coe_smul_of_tower, mul_smul_comm, hx]

end BaseChange

section Free

variable {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F] [Module R F]

/-- **The wedge with the complementary basis vectors.** If `e` is a basis of `F` indexed by
`Fin (n + 1)` and the `m`-th coordinate of `x` is nonzero, then
`x ∧ e_0 ∧ ⋯ ∧ ê_m ∧ ⋯ ∧ e_n ≠ 0`: its top coordinate is `sign σ · e.repr x m` for the
permutation `σ = Fin.cons m m.succAbove`. -/
theorem ι_mul_ιMulti_succAbove_ne_zero {n : ℕ} (e : Module.Basis (Fin (n + 1)) R F) (x : F)
    (m : Fin (n + 1)) (hx : e.repr x m ≠ 0) :
    ExteriorAlgebra.ι R x * ExteriorAlgebra.ιMulti R n (e ∘ m.succAbove) ≠ 0 := by
  intro h
  have hinj : Function.Injective (Fin.cons m m.succAbove : Fin (n + 1) → Fin (n + 1)) :=
    Fin.cons_injective_iff.mpr ⟨fun ⟨z, hz⟩ => Fin.succAbove_ne m z hz,
      Fin.succAbove_right_injective⟩
  let σ : Equiv.Perm (Fin (n + 1)) :=
    Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hσ : (Fin.cons (e m) (e ∘ m.succAbove) : Fin (n + 1) → F) = e ∘ σ :=
    (Fin.comp_cons e m m.succAbove).symm
  have hcoord : ∀ i, e.det (Fin.cons (e i) (e ∘ m.succAbove)) =
      if i = m then ((Equiv.Perm.sign σ : ℤ) : R) else 0 := by
    intro i
    split_ifs with him
    · rw [him, hσ, AlternatingMap.map_perm, e.det_self, Units.smul_def, zsmul_eq_mul, mul_one]
    · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq him
      refine e.det.map_eq_zero_of_eq _ (i := 0) (j := z.succ) ?_ (Fin.succ_ne_zero z).symm
      rw [Fin.cons_zero, Fin.cons_succ, Function.comp_apply, hz]
  have hwedge : wedgeLeft n x (ιMulti R n (e ∘ m.succAbove)) =
      ∑ i, e.repr x i • ιMulti R (n + 1) (Fin.cons (e i) (e ∘ m.succAbove)) := by
    apply Subtype.ext
    conv_lhs => rw [coe_wedgeLeft, ← e.sum_repr x]
    rw [map_sum, Finset.sum_mul, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_mul_assoc, Submodule.coe_smul, ← coe_wedgeLeft, wedgeLeft_ιMulti]
  have h0 : wedgeLeft n x (ιMulti R n (e ∘ m.succAbove)) = 0 :=
    Subtype.ext (by rw [coe_wedgeLeft, ιMulti_apply_coe]; exact h)
  have htop := congrArg e.exteriorPowerTopEquiv (hwedge.symm.trans h0)
  rw [map_sum, map_zero] at htop
  simp only [map_smul, Module.Basis.exteriorPowerTopEquiv_ιMulti, hcoord, smul_eq_mul, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at htop
  exact hx ((IsUnit.map (Int.castRingHom R) (Equiv.Perm.sign σ).isUnit).mul_left_eq_zero.mp htop)

end Free

section Localization

variable {A : Type u} [CommRing A] {Q : Type v} [AddCommGroup Q] [Module A Q]
  [Module.Finite A Q] [Module.Projective A Q]

/-- **Nondegeneracy of the wedge pairing in top degree.** If `Q` is finite projective of rank
`n + 1` at every prime and `q ≠ 0`, then `q ∧ x ≠ 0` for some `x ∈ ⋀[A]^n Q`. -/
theorem exists_wedgeLeft_ne_zero {n : ℕ} (hr : ∀ p, Module.rankAtStalk (R := A) Q p = n + 1)
    {q : Q} (hq : q ≠ 0) : ∃ x : ⋀[A]^n Q, wedgeLeft n q x ≠ 0 := by
  by_contra! H
  apply hq
  refine Module.eq_zero_of_localization_maximal (fun P _ => Localization.AtPrime P ⊗[A] Q)
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) Q 1) q fun P _ => ?_
  by_contra hq'
  have : Module.Free (Localization.AtPrime P) (Localization.AtPrime P ⊗[A] Q) :=
    Module.free_of_flat_of_isLocalRing
  have hrank : Module.finrank (Localization.AtPrime P) (Localization.AtPrime P ⊗[A] Q) = n + 1 :=
    (Module.rankAtStalk_eq_finrank_tensorProduct (⟨P, inferInstance⟩ : PrimeSpectrum A)).symm.trans
      (hr _)
  let e := Module.finBasisOfFinrankEq (Localization.AtPrime P)
    (Localization.AtPrime P ⊗[A] Q) hrank
  obtain ⟨m, hm⟩ : ∃ m, e.repr ((1 : Localization.AtPrime P) ⊗ₜ[A] q) m ≠ 0 := by
    by_contra! h0
    exact hq' ((LinearEquiv.map_eq_zero_iff e.repr).mp (Finsupp.ext h0))
  apply ι_mul_ιMulti_succAbove_ne_zero e _ m hm
  obtain ⟨z, hz⟩ := liftBaseChange_toBaseChange_surjective A (Localization.AtPrime P) n Q
    (ιMulti (Localization.AtPrime P) n (e ∘ m.succAbove))
  have key : ∀ z : Localization.AtPrime P ⊗[A] ⋀[A]^n Q,
      ExteriorAlgebra.ι (Localization.AtPrime P) ((1 : Localization.AtPrime P) ⊗ₜ[A] q) *
        ((toBaseChange A (Localization.AtPrime P) n Q).liftBaseChange (Localization.AtPrime P) z :
          ExteriorAlgebra (Localization.AtPrime P) (Localization.AtPrime P ⊗[A] Q)) = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      rw [LinearMap.liftBaseChange_tmul, Submodule.coe_smul, mul_smul_comm,
        ← coe_toBaseChange_wedgeLeft, H x, map_zero, ZeroMemClass.coe_zero, smul_zero]
    | add z₁ z₂ h₁ h₂ => rw [map_add, Submodule.coe_add, mul_add, h₁, h₂, add_zero]
  have h := key z
  rwa [hz, ιMulti_apply_coe] at h

end Localization

section Kernel

variable {A : Type u} [CommRing A] {V : Type v} [AddCommGroup V] [Module A V]

/-- **A quotient of constant rank `n + 1` is determined by its top exterior power**: `v ∈ N`
exactly when `v ∧ η` lies in the kernel of `⋀[A]^(n+1) V → ⋀[A]^(n+1) (V ⧸ N)` for every
`η ∈ ⋀[A]^n V`. -/
theorem mem_iff_forall_wedgeLeft_mem_ker (N : Submodule A V) [Module.Finite A (V ⧸ N)]
    [Module.Projective A (V ⧸ N)] {n : ℕ}
    (hr : ∀ p, Module.rankAtStalk (R := A) (V ⧸ N) p = n + 1) (v : V) :
    v ∈ N ↔ ∀ η : ⋀[A]^n V, wedgeLeft n v η ∈ LinearMap.ker (map (n + 1) N.mkQ) := by
  constructor
  · intro hv η
    rw [LinearMap.mem_ker, map_wedgeLeft, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero N).mpr hv, wedgeLeft_zero]
  · intro H
    by_contra hv
    have hq : N.mkQ v ≠ 0 := by
      rwa [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨x, hx⟩ := exists_wedgeLeft_ne_zero hr hq
    obtain ⟨η, rfl⟩ := exteriorPower.map_surjective (n := n) N.mkQ_surjective x
    exact hx (by rw [← map_wedgeLeft]; exact H η)

end Kernel

end exteriorPower
