/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Filtration
public import Aglib.RingTheory.FiniteLength.Support
public import Aglib.RingTheory.PrimeFiltration.Support
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Principal Euler finiteness from actual support

Supporting auxiliary for `K2-018#prop:k2018-arithmetic-characters`
(`research/exposes/K2/018/expose.tex`), source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

Finite scalar homology for actual subquotients and prime-filtration factors is derived from
finite M/tM over a Noetherian ring.

This module supplies the stated local algebraic construction; it does not
claim a full original face-cycle or motivic comparison theorem.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.PrincipalEulerSupport` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`5dd0cee73230a6d3cf58f6ac525d8aa880a5bc6e7ad08eb823b6f0e2913099eb`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Module
universe u v
variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

open scoped Pointwise in
/-- The actual scalar cokernel has exactly the support cut out by t. -/
theorem support_scalarCokernel [Module.Finite A M] (t : A) :
    Module.support A (ScalarCokernel M t) =
      Module.support A M ∩ PrimeSpectrum.zeroLocus ({t} : Set A) := by
  have hr : LinearMap.range (LinearMap.lsmul A M t) = t • (⊤ : Submodule A M) := by
    ext x
    rw [Submodule.mem_smul_pointwise_iff_exists]
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_top, true_and]
  change Module.support A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) = _
  rw [hr]
  exact Module.support_quotSMulTop t

theorem scalar_mem_annihilator_kernel (t : A) :
    t ∈ Module.annihilator A (ScalarKernel M t) := by
  apply Module.mem_annihilator.mpr
  intro x
  apply Subtype.ext
  exact x.property

theorem scalar_mem_annihilator_cokernel (t : A) :
    t ∈ Module.annihilator A (ScalarCokernel M t) := by
  apply Module.mem_annihilator.mpr
  intro x
  induction x using Quotient.inductionOn' with
  | h m =>
    change (Submodule.Quotient.mk (t • m) : ScalarCokernel M t) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨m, rfl⟩

variable {N : Type*} [AddCommGroup N] [Module A N]

/-- Finite scalar homology is inherited by every finite module whose support
is contained in the original module's support. In particular this covers
every actual filtration submodule and prime factor. -/
theorem finitePrincipal_of_support_subset [IsNoetherianRing A]
    [Module.Finite A M] [Module.Finite A N] (t : A)
    (hM : Module.length A (ScalarCokernel M t) ≠ ⊤)
    (hs : Module.support A N ⊆ Module.support A M) : FinitePrincipal N t := by
  have hm : ∀ p : PrimeSpectrum A, p ∈ Module.support A N → t ∈ p.asIdeal →
      p.asIdeal.IsMaximal := by
    intro p hp ht
    apply isMaximal_of_mem_support_of_length_ne_top hM p
    rw [support_scalarCokernel]
    exact ⟨hs hp, Set.singleton_subset_iff.mpr ht⟩
  constructor
  · apply length_ne_top_of_support_isMaximal
    intro p hp
    exact hm p
      ((Module.support_subset_of_injective (ScalarKernel N t).subtype
        (Submodule.subtype_injective _)) hp)
      ((Module.annihilator_le_of_mem_support hp) (scalar_mem_annihilator_kernel t))
  · apply length_ne_top_of_support_isMaximal
    intro p hp
    exact hm p
      ((Module.support_subset_of_surjective (LinearMap.range (LinearMap.lsmul A N t)).mkQ
        (Submodule.mkQ_surjective _)) hp)
      ((Module.annihilator_le_of_mem_support hp) (scalar_mem_annihilator_cokernel t))

namespace PrimeFiltrationFrom

/-- Actual finite filtrations require no separately assumed finite scalar
homology on their submodules or quotient factors. -/
theorem finitePrincipal_terms [IsNoetherianRing A] [Module.Finite A M]
    {U : Submodule A M} (D : PrimeFiltrationFrom M U) (t : A)
    (hM : Module.length A (ScalarCokernel M t) ≠ ⊤) :
    (∀ V : Submodule A M, FinitePrincipal V t) ∧
      (∀ p ∈ D.primes, FinitePrincipal (A ⧸ p) t) := by
  constructor
  · intro V
    exact finitePrincipal_of_support_subset t hM
      (Module.support_subset_of_injective V.subtype (Submodule.subtype_injective V))
  · intro p hp
    exact finitePrincipal_of_support_subset t hM (D.primeFactor_support_subset p hp)

theorem principalEuler_eq_sum_of_finite_cokernel [IsNoetherianRing A] [Module.Finite A M]
    (D : PrimeFiltrationFrom M ⊥) (t : A)
    (hM : Module.length A (ScalarCokernel M t) ≠ ⊤) :
    principalEuler (N := M) t =
      (D.primes.map fun p => principalEuler (N := A ⧸ p) t).sum := by
  have hh := D.finitePrincipal_terms t hM
  have he := D.principalEuler_eq_sum t hh.1 hh.2
  have hz : principalEuler (N := (⊥ : Submodule A M)) t = 0 :=
    principalEuler_zero_of_finite_length t (by simp)
  simpa only [hz, zero_add] using he

end PrimeFiltrationFrom

end Module
