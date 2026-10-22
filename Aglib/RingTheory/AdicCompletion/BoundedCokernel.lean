/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BoundedPullback
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Original elements surject onto bounded quotients of a completion

For a finitely generated defining ideal, approximation at a single stage
proves that an original module already surjects onto any bounded-torsion
quotient of its completion. The modules need not be finitely generated. The statements
retain the actual original map and actual cokernel quotient. Neither faithful
flatness nor finiteness over the original ring is asserted for a completion.
-/

@[expose] public section

namespace AdicCompletion

variable {R N C : Type*} [CommRing R] (I : Ideal R)
  [AddCommGroup N] [Module R N] [AddCommGroup C] [Module R C]

/-- Original elements surject onto a bounded-torsion quotient of a completion.
The finitely generated ideal hypothesis identifies the algebraic power
with the evaluation kernel. This is not a faithful-flatness argument. -/
theorem surjective_comp_of_of_pow_smul_eq_bot (hI : I.FG) (t : ℕ)
    (q : AdicCompletion I N →ₗ[R] C) (hq : Function.Surjective q)
    (hC : I ^ t • (⊤ : Submodule R C) = ⊥) :
    Function.Surjective (q.comp (of I N)) := by
  intro c
  obtain ⟨x, rfl⟩ := hq c
  obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective _ (eval I N t x)
  have hdiff : x - of I N n ∈ I ^ t • (⊤ : Submodule R (AdicCompletion I N)) := by
    rw [pow_smul_top_eq_ker_eval (M := N) hI]
    change eval I N t (x - of I N n) = 0
    rw [map_sub, eval_of, Submodule.mkQ_apply, ← hn, sub_self]
  have hz := Submodule.smul_top_le_comap_smul_top (I ^ t) q hdiff
  change q (x - of I N n) ∈ I ^ t • (⊤ : Submodule R C) at hz
  rw [hC] at hz
  have hz0 : q (x - of I N n) = 0 := hz
  have heq : q x = q (of I N n) := sub_eq_zero.mp (by simpa only [map_sub] using hz0)
  exact ⟨n, heq.symm⟩

end AdicCompletion

namespace LinearMap

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- The cokernel range bound is literal annihilation of the actual quotient. -/
theorem smul_top_quotient_range_eq_bot (f : M →ₗ[R] P) (J : Ideal R)
    (h : J • (⊤ : Submodule R P) ≤ f.range) :
    J • (⊤ : Submodule R (P ⧸ f.range)) = ⊥ := by
  have hm := Submodule.map_mono (f := f.range.mkQ) h
  simp only [Submodule.map_smul'', Submodule.map_top,
    Submodule.range_mkQ, Submodule.mkQ_map_self] at hm
  exact le_antisymm hm bot_le

/-- The actual pullback projection has precisely the kernel of the original
map into the original cokernel. This is the right half of its four-term sequence. -/
theorem pullbackKernelSnd_exact_cokernel (f : M →ₗ[R] P) (g : N →ₗ[R] P) :
    Function.Exact (pullbackKernelSnd f g) (f.range.mkQ.comp g) := by
  intro n
  constructor
  · intro hn
    have hn' : g n ∈ f.range := (Submodule.Quotient.mk_eq_zero _).mp hn
    obtain ⟨m, hm⟩ := hn'
    refine ⟨⟨(m, n), ?_⟩, rfl⟩
    change f m + -(g n) = 0
    rw [hm, add_neg_cancel]
  · rintro ⟨x, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨x.val.1, ?_⟩
    exact LinearMap.congr_fun (pullbackKernel_comm f g) x

/-- The original kernel embeds into the native pullback. -/
theorem kerToPullbackKernel_injective (f : M →ₗ[R] P) (g : N →ₗ[R] P) :
    Function.Injective (kerToPullbackKernel f g) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : pullbackKernel f g => z.val.1) h

end LinearMap
