/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Module length on exact sequences and endomorphisms

Integer length is the integer cast of ENat.toNat and is defined for every module. Additivity
retains an explicit finite-length hypothesis. A finite-length module endomorphism has equal
actual kernel and cokernel lengths.

## Extraction basis

Transferred subsets of `R5Lab.RingTheory.LocalLength.PrincipalEulerAdditivity` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, source SHA-256
`26ee2397a837a665bc1b1c6f248fdacdc0d43009ea147acb68137233d7c5446d`. Objects, universes,
canonical maps and
actual premises are retained; declarations use native mathematical namespaces.

The endomorphism cancellation theorem is transferred from
`R5Lab.RingTheory.LocalLength.PrincipalEuler` on the same R5 revision.
-/

@[expose] public section

noncomputable section

namespace Module
universe u v w z
variable {A : Type u} [CommRing A]
variable {U : Type v} {V : Type w} {W : Type z}
variable [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
variable [AddCommGroup W] [Module A W]

/-- Integer length, to be used only with an explicit finite-length hypothesis. -/
def intLength (N : Type*) [AddCommGroup N] [Module A N] : ℤ :=
  ((Module.length A N).toNat : ℤ)

theorem intLength_add_of_exact (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (hV : Module.length A V ≠ ⊤) :
    intLength (A := A) V = intLength (A := A) U + intLength (A := A) W := by
  have hU : Module.length A U ≠ ⊤ :=
    ne_top_of_le_ne_top hV (Module.length_le_of_injective f hf)
  have hW : Module.length A W ≠ ⊤ :=
    ne_top_of_le_ne_top hV (Module.length_le_of_surjective g hg)
  unfold intLength
  rw [Module.length_eq_add_of_exact f g hf hg hex, ENat.toNat_add hU hW, Nat.cast_add]

theorem intLength_exact_pair (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hex : Function.Exact f g) (hV : Module.length A V ≠ ⊤) :
    intLength (A := A) V = intLength (A := A) (LinearMap.range f) +
      intLength (A := A) (LinearMap.range g) := by
  have h : Function.Exact (LinearMap.range f).subtype g.rangeRestrict := by
    intro x
    constructor
    · intro hx
      have hgx : g x = 0 := congrArg Subtype.val hx
      obtain ⟨y, hy⟩ := (hex x).mp hgx
      exact ⟨⟨f y, ⟨y, rfl⟩⟩, hy⟩
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      obtain ⟨z, hz⟩ := y.property
      change g y = 0
      rw [← hz]
      exact hex.apply_apply_eq_zero z
  have hg : Function.Surjective g.rangeRestrict := by
    rintro ⟨w, v, hv⟩
    exact ⟨v, Subtype.ext hv⟩
  exact intLength_add_of_exact _ _ (Submodule.subtype_injective _) hg h hV

section Endomorphisms
variable {N : Type v} [AddCommGroup N] [Module A N]

/-- For a finite-length module, every endomorphism has equal kernel and cokernel lengths.
This is the cancellation of zero-dimensional factors.

Source mapping: supporting generalized local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded prerequisite subset: for arbitrary A and N, Module.length A N != infinity gives
equal ENat kernel and cokernel lengths for every endomorphism; no injectivity or
flatness premise is used. -/
theorem length_kernel_eq_cokernel (f : N →ₗ[A] N) (hN : Module.length A N ≠ ⊤) :
    Module.length A (LinearMap.ker f) = Module.length A (N ⧸ LinearMap.range f) := by
  have h₁ := Module.length_eq_add_of_exact (LinearMap.ker f).subtype
    (LinearMap.ker f).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [f.quotKerEquivRange.length_eq] at h₁
  have h₂ := Module.length_eq_add_of_exact (LinearMap.range f).subtype
    (LinearMap.range f).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hr : Module.length A (LinearMap.range f) ≠ ⊤ :=
    ne_top_of_le_ne_top hN (Module.length_le_of_injective (LinearMap.range f).subtype
      (Submodule.subtype_injective _))
  apply ENat.add_left_injective_of_ne_top hr
  exact h₁.symm.trans (h₂.trans (add_comm _ _))

end Endomorphisms
end Module
