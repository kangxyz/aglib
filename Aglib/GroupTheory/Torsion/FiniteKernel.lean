/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupTheory.Torsion.BoundedTower
public import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# Finite kernels on compatible power-torsion towers


Source: `R5Lab.Aglib.GroupTheory.Torsion.FiniteKernel`.
Packet SHA-256:
`53a802bbd96820c29e525969eb59ade794d9b5a9f201c255267c6ccafb492207`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
namespace AddMonoidHom
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem tower_zero_of_finite_kernel (q : ℕ) (f : A →+ B) [Finite f.ker]
    (x : ℕ → A) (hstep : ∀ n, q • x (n + 1) = x n)
    (htorsion : ∀ n, q ^ n • x n = 0) (hkernel : ∀ n, f (x n) = 0) :
    ∀ n, x n = 0 := by
  classical
  let S := {a : f.ker // ∃ m : ℕ, q ^ m • (a : A) = 0}
  let : Fintype S := Fintype.ofFinite S
  let e (a : S) : ℕ := a.property.choose
  have he (a : S) : q ^ e a • ((a.val : f.ker) : A) = 0 := a.property.choose_spec
  let E := Finset.univ.sup e
  apply AddCommGroup.BoundedTower.eq_zero_of_compatible_bounded q E x hstep
  intro n
  let a : S := ⟨⟨x n, by simpa using hkernel n⟩, ⟨n, htorsion n⟩⟩
  have hle : e a ≤ E := Finset.le_sup (Finset.mem_univ a)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  change q ^ E • ((a.val : f.ker) : A) = 0
  rw [hd, pow_add, mul_nsmul]
  rw [he a, smul_zero]

theorem towers_equal_of_finite_kernel (q : ℕ) (f : A →+ B) [Finite f.ker]
    (x y : ℕ → A) (hxstep : ∀ n, q • x (n + 1) = x n)
    (hystep : ∀ n, q • y (n + 1) = y n)
    (hxtorsion : ∀ n, q ^ n • x n = 0) (hytorsion : ∀ n, q ^ n • y n = 0)
    (himage : ∀ n, f (x n) = f (y n)) : ∀ n, x n = y n := by
  have hzero := tower_zero_of_finite_kernel q f (fun n => x n - y n)
    (fun n => by simp only [smul_sub, hxstep, hystep])
    (fun n => by simp only [smul_sub, hxtorsion, hytorsion, sub_self])
    (fun n => by simp only [map_sub, himage, sub_self])
  exact fun n => sub_eq_zero.mp (hzero n)

end AddMonoidHom
