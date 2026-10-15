/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Prime filtrations of finite modules

A finite module over a Noetherian ring admits a filtration by prime cyclic quotients. The
filtration records submodules, quotient equivalences and the actual prime factors used by
local-length and Euler computations.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.PrimeFiltration` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`db7d2a0e0feca332afce29c5912aa3245bbc0812ffbbad273c98da5219662b62`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
namespace Module
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
section Cyclic
variable (M : Type v) [AddCommGroup M] [Module A M] [Nontrivial M]

/-- A nonzero module over a Noetherian ring contains an actual cyclic prime
quotient. This is the step used to build a finite prime filtration; there is
no projectivity or freeness premise on A/p. -/
theorem exists_prime_cyclic_submodule :
    ∃ (p : Ideal A) (N : Submodule A M),
      p.IsPrime ∧ N ≠ ⊥ ∧ Nonempty ((A ⧸ p) ≃ₗ[A] N) := by
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty A M
  obtain ⟨hp', x, hpx⟩ := isAssociatedPrime_iff.mp hp
  let f : A →ₗ[A] M := LinearMap.toSpanSingleton A M x
  have hk : LinearMap.ker f = p := by
    ext a
    change a • x = 0 ↔ a ∈ p
    rw [hpx]
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
  have hr : LinearMap.range f ≠ ⊥ := by
    intro h
    have hx : x = 0 := by
      have hzmem : f 1 ∈ (⊥ : Submodule A M) := by
        rw [← h]
        exact LinearMap.mem_range_self f 1
      have hz : f 1 = 0 := by simpa only [Submodule.mem_bot] using hzmem
      simpa only [f, LinearMap.toSpanSingleton_apply_one] using hz
    apply hp'.ne_top
    rw [hpx, hx]
    ext a
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_zero, Submodule.mem_top]
  refine ⟨p, LinearMap.range f, hp', hr, ⟨?_⟩⟩
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans f.quotKerEquivRange

end Cyclic

variable (M : Type v) [AddCommGroup M] [Module A M]

/-- An actual finite prime filtration above an ambient submodule. Each step
carries the literal successive-quotient isomorphism, rather than a length or
Euler equality. -/
inductive PrimeFiltrationFrom : Submodule A M → Type (max u v)
  | top : PrimeFiltrationFrom ⊤
  | step {U V : Submodule A M} (hUV : U < V) (p : Ideal A) (hp : p.IsPrime)
      (e : (V ⧸ U.comap V.subtype) ≃ₗ[A] A ⧸ p)
      (tail : PrimeFiltrationFrom V) : PrimeFiltrationFrom U

/-- The first-isomorphism-theorem identification used to lift a cyclic prime
submodule of M/U to the actual next submodule of M. -/
def _root_.Submodule.comapMkQQuotientEquiv (U : Submodule A M) (N : Submodule A (M ⧸ U)) :
    ((N.comap U.mkQ) ⧸ U.comap (N.comap U.mkQ).subtype) ≃ₗ[A] N := by
  let V := N.comap U.mkQ
  let f : V →ₗ[A] N := (U.mkQ.comp V.subtype).codRestrict N fun x => x.property
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨m, hm⟩ := Submodule.mkQ_surjective U x
    refine ⟨⟨m, ?_⟩, Subtype.ext hm⟩
    change U.mkQ m ∈ N
    rw [hm]
    exact x.property
  have hk : LinearMap.ker f = U.comap V.subtype := by
    ext x
    constructor
    · intro hx
      have hz : U.mkQ x = 0 := congrArg Subtype.val hx
      exact (Submodule.Quotient.mk_eq_zero U).mp hz
    · intro hx
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero U).mpr hx
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)

/-- Noetherian induction builds the complete finite prime filtration, using
an actual associated-prime cyclic submodule in each nonzero remaining quotient. -/
theorem nonempty_primeFiltrationFrom [IsNoetherian A M] (U : Submodule A M) :
    Nonempty (PrimeFiltrationFrom (A := A) M U) := by
  apply IsNoetherian.induction (P := fun U => Nonempty (PrimeFiltrationFrom (A := A) M U)) _ U
  intro U ih
  by_cases hU : U = ⊤
  · subst U
    exact ⟨PrimeFiltrationFrom.top⟩
  · let : Nontrivial (M ⧸ U) := Submodule.Quotient.nontrivial_iff.mpr hU
    obtain ⟨p, N, hp, hN, ⟨e⟩⟩ := exists_prime_cyclic_submodule (A := A) (M ⧸ U)
    let V := N.comap U.mkQ
    have hNgt : (⊥ : Submodule A (M ⧸ U)) < N := bot_lt_iff_ne_bot.mpr hN
    have hUV : U < V := by
      have h := (Submodule.comapMkQOrderEmbedding U).strictMono hNgt
      simpa only [Submodule.comapMkQOrderEmbedding_eq, Submodule.comap_bot,
        Submodule.ker_mkQ] using h
    obtain ⟨tail⟩ := ih V hUV
    exact ⟨PrimeFiltrationFrom.step hUV p hp
      ((Submodule.comapMkQQuotientEquiv M U N).trans e.symm) tail⟩

/-- Every finite module over a Noetherian ring admits the actual certificate. -/
theorem nonempty_primeFiltration [Module.Finite A M] :
    Nonempty (PrimeFiltrationFrom (A := A) M ⊥) :=
  nonempty_primeFiltrationFrom M ⊥

end Module
