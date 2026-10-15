/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Aglib.RingTheory.PrimeFiltration.Primes

/-!
# Principal Euler expressions along prime filtrations

Finite scalar kernel/cokernel conditions propagate along a chosen prime filtration. Additivity
expresses the module Euler value as the sum of its actual prime-factor Euler values.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.PrincipalEulerFiltration` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`860f378ac24bc0033903038bcae32ff592ede183c1c0378541bfd5a3a092a1f6`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
namespace Module
universe u v
variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- Euler length is computed from actual successive quotient modules in any
finite filtration. The hypotheses supply quotient isomorphisms and finite
homology lengths, not the resulting Euler sum. Prime-factor quotient modules
need not be free or regular for the principal scalar. -/
theorem principalEuler_of_quotientFiltration
    (t : A) (n : ℕ) (F : Fin (n + 1) → Submodule A M) (P : Fin n → Ideal A)
    (hmono : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    (e : ∀ i : Fin n,
      ((F i.succ) ⧸ (F i.castSucc).comap (F i.succ).subtype) ≃ₗ[A] A ⧸ P i)
    (hF : ∀ i, FinitePrincipal (F i) t)
    (hP : ∀ i, FinitePrincipal (A ⧸ P i) t) :
    principalEuler (N := M) t = ∑ i : Fin n, principalEuler (N := A ⧸ P i) t := by
  have h₀ : principalEuler (N := (F 0)) t = 0 := by
    apply principalEuler_zero_of_finite_length t
    rw [hzero]
    simp only [Module.length_eq_zero, ne_eq, ENat.zero_ne_top, not_false_eq_true]
  have hs : ∀ i : Fin n, principalEuler (N := (F i.succ)) t =
      principalEuler (N := (F i.castSucc)) t + principalEuler (N := A ⧸ P i) t := by
    intro i
    have hle : F i.castSucc ≤ F i.succ := hmono (by
      change i.val ≤ i.val + 1
      omega)
    let C : Submodule A (F i.succ) := (F i.castSucc).comap (F i.succ).subtype
    let f : (F i.castSucc) →ₗ[A] (F i.succ) := Submodule.inclusion hle
    have hf : Function.Injective f := Submodule.inclusion_injective hle
    have hex : Function.Exact f C.mkQ := by
      intro x
      constructor
      · intro hx
        have hm : (x : M) ∈ F i.castSucc := (Submodule.Quotient.mk_eq_zero C).mp hx
        exact ⟨⟨x, hm⟩, Subtype.ext rfl⟩
      · rintro ⟨y, rfl⟩
        apply (Submodule.Quotient.mk_eq_zero C).mpr
        exact y.property
    have hC : FinitePrincipal ((F i.succ) ⧸ C) t :=
      (finitePrincipal_congr (e i) t).mpr (hP i)
    have h := principalEuler_add_of_exact f C.mkQ hf (Submodule.mkQ_surjective C)
      hex t (hF i.castSucc) (hF i.succ) hC
    exact h.trans (congrArg (principalEuler (N := (F i.castSucc)) t + ·)
      (principalEuler_congr (e i) t))
  have hall := Int.integer_telescope n (fun i => principalEuler (N := (F i)) t)
    (fun i => principalEuler (N := A ⧸ P i) t) h₀ hs
  have hend : principalEuler (N := (F (Fin.last n))) t = principalEuler (N := M) t := by
    rw [htop]
    exact principalEuler_congr (Submodule.topEquiv (R := A) (M := M)) t
  exact hend.symm.trans hall

theorem principalEuler_add_of_submodule_le (t : A) (U V : Submodule A M) (hUV : U ≤ V)
    (hU : FinitePrincipal U t) (hV : FinitePrincipal V t)
    (hQ : FinitePrincipal (V ⧸ U.comap V.subtype) t) :
    principalEuler (N := V) t = principalEuler (N := U) t +
      principalEuler (N := V ⧸ U.comap V.subtype) t := by
  let C : Submodule A V := U.comap V.subtype
  let f : U →ₗ[A] V := Submodule.inclusion hUV
  have hex : Function.Exact f C.mkQ := by
    intro x
    constructor
    · intro hx
      have hm : (x : M) ∈ U := (Submodule.Quotient.mk_eq_zero C).mp hx
      exact ⟨⟨x, hm⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero C).mpr
      exact y.property
  exact principalEuler_add_of_exact f C.mkQ (Submodule.inclusion_injective hUV)
    (Submodule.mkQ_surjective C) hex t hU hV hQ

namespace PrimeFiltrationFrom

/-- The complete actual prime-filtration certificate computes Euler length.
Only finite scalar-homology lengths are supplied; no Euler or multiplicity sum
is an input, and the certificate itself exists by Noetherian induction. -/
theorem principalEuler_eq_sum {U : Submodule A M} (D : PrimeFiltrationFrom M U) (t : A)
    (hN : ∀ N : Submodule A M, FinitePrincipal N t)
    (hP : ∀ p ∈ D.primes, FinitePrincipal (A ⧸ p) t) :
    principalEuler (N := M) t = principalEuler (N := U) t +
      (D.primes.map fun p => principalEuler (N := A ⧸ p) t).sum := by
  induction D with
  | top =>
    simpa only [primes, List.map_nil, List.sum_nil, add_zero] using
      (principalEuler_congr (Submodule.topEquiv (R := A) (M := M)) t).symm
  | @step U V hUV p hp e tail ih =>
    have hpp : FinitePrincipal (A ⧸ p) t := hP p (by simp [primes])
    have hpt : ∀ q ∈ tail.primes, FinitePrincipal (A ⧸ q) t := by
      intro q hq
      exact hP q (by simp only [primes]; exact List.mem_cons_of_mem _ hq)
    have hC := (finitePrincipal_congr e t).mpr hpp
    have hstep := principalEuler_add_of_submodule_le t U V hUV.le (hN U) (hN V) hC
    rw [principalEuler_congr e t] at hstep
    have hi := ih hpt
    rw [hstep] at hi
    simpa only [primes, List.map_cons, List.sum_cons, add_assoc] using hi

end PrimeFiltrationFrom

end Module
