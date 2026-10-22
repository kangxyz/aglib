/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BoundedPullback
public import Aglib.RingTheory.AdicCompletion.BoundedCokernel
public import Aglib.RingTheory.AdicCompletion.BoundedTorsion
public import Aglib.RingTheory.AdicCompletion.ExactPair

/-!
# Cartesian completion squares for bounded maps

An original finite map with kernel and cokernel killed by a power of the
completion ideal is recovered by its completion square. This is not a claim
that completion is faithful on arbitrary finite modules.
-/

@[expose] public noncomputable section

namespace AdicCompletion

universe u
variable {R F N : Type u} [CommRing R] (I : Ideal R)
  [AddCommGroup F] [Module R F] [AddCommGroup N] [Module R N]

/-- The original map into its native completion square. -/
def completionPullbackMap (a : F →ₗ[R] N) :
    F →ₗ[R] LinearMap.pullbackKernel ((map I a).restrictScalars R) (of I N) :=
  LinearMap.liftPullbackKernel _ _ (of I F) a (by
    apply LinearMap.ext
    intro x
    exact map_of I a x)

@[simp]
theorem completionPullbackMap_fst (a : F →ₗ[R] N) (x : F) :
    (completionPullbackMap I a x).val.1 = of I F x := rfl

@[simp]
theorem completionPullbackMap_snd (a : F →ₗ[R] N) (x : F) :
    (completionPullbackMap I a x).val.2 = a x := rfl

variable [IsNoetherianRing R] [Module.Finite R F] [Module.Finite R N]

/-- Bounded original defects make the completion square cartesian. Both
bounds concern the same ideal used for completion. -/
theorem completionPullbackMap_bijective (a : F →ₗ[R] N) (t : ℕ)
    (hker : I ^ t • a.ker = ⊥)
    (hcoker : I ^ t • (⊤ : Submodule R N) ≤ a.range) :
    Function.Bijective (completionPullbackMap I a) := by
  let K := a.ker
  let C := N ⧸ a.range
  let k : K →ₗ[R] F := a.ker.subtype
  let q : N →ₗ[R] C := a.range.mkQ
  have hK : I ^ t • (⊤ : Submodule R K) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Submodule.smul_le.mpr
    intro r hr x _
    have hz := Submodule.smul_mem_smul hr (show x.val ∈ a.ker from x.property)
    rw [hker] at hz
    change r • x = 0
    apply Subtype.ext
    exact hz
  let : IsAdicComplete I K := IsAdicComplete.of_pow_smul_eq_bot I t hK
  let : IsAdicComplete I C := IsAdicComplete.of_pow_smul_eq_bot I t
    (LinearMap.smul_top_quotient_range_eq_bot a (I ^ t) hcoker)
  have hka : Function.Exact k a := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact x.property
  have haq : Function.Exact a q := fun x => Submodule.Quotient.mk_eq_zero _
  have hkhat := map_injective I (f := k) Subtype.val_injective
  have hexa := map_exact_pair I k a hka
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hax : a x = 0 := congrArg (fun z => z.val.2) hx
    have hox : of I F x = 0 := congrArg (fun z => z.val.1) hx
    let y : K := ⟨x, hax⟩
    have hy : of I K y = 0 := by
      apply hkhat
      rw [map_of, _root_.map_zero]
      exact hox
    have hy0 : y = 0 := (of_bijective I K).injective (hy.trans (_root_.map_zero _).symm)
    exact congrArg Subtype.val hy0
  · intro z
    have hz : map I a z.val.1 = of I N z.val.2 := by
      have h := z.property
      change map I a z.val.1 + -(of I N z.val.2) = 0 at h
      exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)
    have hqn : q z.val.2 = 0 := by
      apply (of_bijective I C).injective
      rw [_root_.map_zero, ← map_of, ← hz, map_comp_apply,
        haq.linearMap_comp_eq_zero, AdicCompletion.map_zero]
      rfl
    obtain ⟨y, hy⟩ := (haq z.val.2).mp hqn
    have hd : map I a (z.val.1 - of I F y) = 0 := by
      rw [_root_.map_sub, hz, map_of, hy, sub_self]
    obtain ⟨w, hw⟩ := (hexa (z.val.1 - of I F y)).mp hd
    obtain ⟨v, rfl⟩ := (of_bijective I K).surjective w
    rw [map_of] at hw
    refine ⟨y + k v, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change of I F (y + k v) = z.val.1
      rw [_root_.map_add, hw, add_comm, sub_add_cancel]
    · change a (y + k v) = z.val.2
      have hv : a (k v) = 0 := v.property
      rw [_root_.map_add, hy, hv, add_zero]

/-- The original finite module, recovered by its bounded completion square. -/
def completionPullbackEquiv (a : F →ₗ[R] N) (t : ℕ)
    (hker : I ^ t • a.ker = ⊥)
    (hcoker : I ^ t • (⊤ : Submodule R N) ≤ a.range) :
    F ≃ₗ[R] LinearMap.pullbackKernel ((map I a).restrictScalars R) (of I N) :=
  LinearEquiv.ofBijective (completionPullbackMap I a)
    (completionPullbackMap_bijective I a t hker hcoker)

end AdicCompletion
