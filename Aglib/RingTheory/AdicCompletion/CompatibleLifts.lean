/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Native completion lifts from original transition-kernel corrections

An original compatible family in a sequence of modules lifts to the native
adic completion if every transition-kernel element can be corrected by the
specified next-stage map on the original ideal power. The proof recursively
constructs exact original lifts whose successive differences lie in `IⁿM`,
then uses the native adic Cauchy sequence and completion maps.

The theorem preserves every original module, transition and linear map. It
needs no Noetherianity, finiteness, coefficient field, completeness or separately
assumed completed-surjectivity statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Submodule

namespace AdicCompletion

universe u v w

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
variable (F : ∀ n, M →ₗ[R] N n) (ρ : ∀ n, N (n + 1) →ₗ[R] N n)
variable (hF : ∀ n, (ρ n).comp (F (n + 1)) = F n)
variable (hcor : ∀ n, (ρ n).ker ≤
  (I ^ n • (⊤ : Submodule R M)).map (F (n + 1)))
variable (x : ∀ n, N n) (hx : ∀ n, ρ n (x (n + 1)) = x n)

private def compatibleCorrection (n : ℕ) (a : M) (ha : F n a = x n) :
    {c : M // c ∈ I ^ n • (⊤ : Submodule R M) ∧
      F (n + 1) c = x (n + 1) - F (n + 1) a} := by
  have he : x (n + 1) - F (n + 1) a ∈ (ρ n).ker := by
    change ρ n (x (n + 1) - F (n + 1) a) = 0
    rw [map_sub, hx n,
      show ρ n (F (n + 1) a) = F n a from LinearMap.congr_fun (hF n) a,
      ha, sub_self]
  let hc : ∃ c : M, c ∈ I ^ n • (⊤ : Submodule R M) ∧
      F (n + 1) c = x (n + 1) - F (n + 1) a :=
    Submodule.mem_map.mp (hcor n he)
  exact ⟨hc.choose, hc.choose_spec⟩

private def compatibleLiftsAt (I : Ideal R)
    (F : ∀ n, M →ₗ[R] N n) (ρ : ∀ n, N (n + 1) →ₗ[R] N n)
    (hF : ∀ n, (ρ n).comp (F (n + 1)) = F n)
    (hcor : ∀ n, (ρ n).ker ≤ (I ^ n • (⊤ : Submodule R M)).map (F (n + 1)))
    (x : ∀ n, N n) (hx : ∀ n, ρ n (x (n + 1)) = x n) (hx0 : x 0 = 0) :
    (n : ℕ) → {a : M // F n a = x n}
  | 0 => ⟨0, (F 0).map_zero.trans hx0.symm⟩
  | n + 1 =>
    let a := compatibleLiftsAt I F ρ hF hcor x hx hx0 n
    let c := compatibleCorrection I F ρ hF hcor x hx n a.val a.property
    ⟨a.val + c.val, by
      rw [map_add, c.property.2, ← add_sub_assoc, add_sub_cancel_left]⟩

private lemma compatibleLiftsAt_smodEq (hx0 : x 0 = 0) (n : ℕ) :
    (compatibleLiftsAt I F ρ hF hcor x hx hx0 n).val ≡
      (compatibleLiftsAt I F ρ hF hcor x hx hx0 (n + 1)).val
        [SMOD (I ^ n • (⊤ : Submodule R M))] := by
  apply SModEq.symm
  rw [SModEq.sub_mem]
  change ((compatibleLiftsAt I F ρ hF hcor x hx hx0 n).val +
      (compatibleCorrection I F ρ hF hcor x hx n
        (compatibleLiftsAt I F ρ hF hcor x hx hx0 n).val
        (compatibleLiftsAt I F ρ hF hcor x hx hx0 n).property).val) -
      (compatibleLiftsAt I F ρ hF hcor x hx hx0 n).val ∈ I ^ n • (⊤ : Submodule R M)
  simpa only [add_sub_cancel_left] using
    (compatibleCorrection I F ρ hF hcor x hx n
      (compatibleLiftsAt I F ρ hF hcor x hx hx0 n).val
      (compatibleLiftsAt I F ρ hF hcor x hx hx0 n).property).property.1

include hF hcor hx in
private theorem exists_compatible_cauchy_lift_zero (hx0 : x 0 = 0) :
    ∃ a : AdicCauchySequence I M, a 0 = 0 ∧ ∀ n, F n (a n) = x n := by
  let a := AdicCauchySequence.mk I M
    (fun n => (compatibleLiftsAt I F ρ hF hcor x hx hx0 n).val)
    (compatibleLiftsAt_smodEq I F ρ hF hcor x hx hx0)
  refine ⟨a, rfl, ?_⟩
  intro n
  exact (compatibleLiftsAt I F ρ hF hcor x hx hx0 n).property

section Unfiltered

variable [Subsingleton (N 0)]

include hF hcor hx in
/-- Every original compatible family has exact original lifts forming a native
adic Cauchy sequence. The first lift is zero, and no surjectivity of a completed
map or additional bound on the kernels of `F n` is assumed. -/
theorem exists_compatible_cauchy_lift :
    ∃ a : AdicCauchySequence I M, a 0 = 0 ∧ ∀ n, F n (a n) = x n :=
  exists_compatible_cauchy_lift_zero I F ρ hF hcor x hx (Subsingleton.elim _ _)

include hF hcor hx in
/-- Every original compatible family lifts to the native adic completion, with
each actual quotient evaluation followed by the original induced linear map
equal to the specified original component. -/
theorem exists_compatible_lift
    (hkill : ∀ n, I ^ n • (⊤ : Submodule R M) ≤ (F n).ker) :
    ∃ z : AdicCompletion I M, ∀ n,
      (I ^ n • (⊤ : Submodule R M)).liftQ (F n) (hkill n)
        (AdicCompletion.eval I M n z) = x n := by
  obtain ⟨a, _, ha⟩ := exists_compatible_cauchy_lift I F ρ hF hcor x hx
  refine ⟨AdicCompletion.mk I M a, ?_⟩
  intro n
  change F n (a n) = x n
  exact ha n

end Unfiltered

private lemma compatible_component_eq_of_le
    (F : ∀ n, M →ₗ[R] N n) (ρ : ∀ n, N (n + 1) →ₗ[R] N n)
    (hF : ∀ n, (ρ n).comp (F (n + 1)) = F n)
    (x : ∀ n, N n) (hx : ∀ n, ρ n (x (n + 1)) = x n)
    {m n : ℕ} (hmn : m ≤ n) (a : M) (ha : F n a = x n) : F m a = x m := by
  revert a
  induction n, hmn using Nat.le_induction with
  | base => intro a ha; exact ha
  | succ n _ ih =>
    intro a ha
    apply ih a
    calc
      F n a = ρ n (F (n + 1) a) := (LinearMap.congr_fun (hF n) a).symm
      _ = ρ n (x (n + 1)) := congrArg (ρ n) ha
      _ = x n := hx n

include hF hcor hx in
/-- A compatible family zero at its original component `q` lifts from the
completion of the original submodule `I^q M`. Its image under the actual native
completion map of the inclusion has every original component equal to `x n`.
No injectivity or image-identification statement for that inclusion is assumed. -/
theorem exists_filtered_compatible_lift
    (hkill : ∀ n, I ^ n • (⊤ : Submodule R M) ≤ (F n).ker)
    (q : ℕ) (hxq : x q = 0) :
    ∃ z : AdicCompletion I ↥(I ^ q • (⊤ : Submodule R M)), ∀ n,
      (I ^ n • (⊤ : Submodule R M)).liftQ (F n) (hkill n)
        (AdicCompletion.eval I M n
          (AdicCompletion.map I ((I ^ q • (⊤ : Submodule R M)).subtype) z)) = x n := by
  let S : Submodule R M := I ^ q • ⊤
  let : ∀ n, AddCommGroup (N (q + n)) := fun n => inferInstance
  let : ∀ n, Module R (N (q + n)) := fun n => inferInstance
  let F' : ∀ n, S →ₗ[R] N (q + n) := fun n => (F (q + n)).comp S.subtype
  let ρ' : ∀ n, N (q + (n + 1)) →ₗ[R] N (q + n) := fun n => ρ (q + n)
  have hF' : ∀ n, (ρ' n).comp (F' (n + 1)) = F' n := by
    intro n
    ext a
    exact LinearMap.congr_fun (hF (q + n)) (a : M)
  have hpow (n : ℕ) : I ^ n • S = I ^ (q + n) • (⊤ : Submodule R M) := by
    dsimp only [S]
    rw [← Submodule.mul_smul, ← pow_add, Nat.add_comm n q]
  have hcor' : ∀ n, (ρ' n).ker ≤
      (I ^ n • (⊤ : Submodule R S)).map (F' (n + 1)) := by
    intro n y hy
    obtain ⟨c, hc, hcy⟩ := Submodule.mem_map.mp (hcor (q + n) hy)
    have hcS : c ∈ S :=
      smul_mono (Ideal.pow_le_pow_right (Nat.le_add_right q n)) le_rfl hc
    apply Submodule.mem_map.mpr
    refine ⟨⟨c, hcS⟩, ?_, hcy⟩
    apply (Submodule.mem_smul_top_iff (I ^ n) S ⟨c, hcS⟩).mpr
    rw [hpow n]
    exact hc
  obtain ⟨a, _, ha⟩ := exists_compatible_cauchy_lift_zero I F' ρ' hF' hcor'
    (fun n => x (q + n)) (fun n => hx (q + n)) hxq
  refine ⟨AdicCompletion.mk I S a, ?_⟩
  intro n
  rw [AdicCompletion.map_mk]
  change F n (a n : M) = x n
  exact compatible_component_eq_of_le F ρ hF x hx (Nat.le_add_left n q) (a n : M) (ha n)

end AdicCompletion
