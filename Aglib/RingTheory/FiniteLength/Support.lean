/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Support
public import Aglib.RingTheory.PrimeFiltration.Support
public import Aglib.RingTheory.PrimeFiltration.Length
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Finite length from maximal support

A finite module over a Noetherian commutative ring has finite length when every prime in its
actual support is maximal. The proof passes through the quotient by the module annihilator; no
local-ring hypothesis is required.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.FiniteLengthSupport` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`ca529353814fbb1acd5d9156c0d8be585a85736fe863f3c841e076fc14c9c623`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Module
universe u v

/-- A finite module over a Noetherian ring has finite length when all primes in
its actual localization support are maximal. This includes the local singleton-support case. -/
theorem finiteLength_of_support_maximal (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : ∀ q : PrimeSpectrum R, q ∈ Module.support R M → q.asIdeal.IsMaximal) :
    IsFiniteLength R M := by
  let I := Module.annihilator R M
  let Q := R ⧸ I
  let : IsNoetherianRing Q := isNoetherianRing_of_surjective R Q
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hdim : Ring.KrullDimLE 0 Q := by
    apply Ring.krullDimLE_zero_iff.mpr
    intro J hJ
    let : J.IsPrime := hJ
    let q : PrimeSpectrum R := ⟨J.comap (Ideal.Quotient.mk I), inferInstance⟩
    have hIq : I ≤ q.asIdeal := by
      intro r hr
      change Ideal.Quotient.mk I r ∈ J
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      exact J.zero_mem
    let : q.asIdeal.IsMaximal := h q (Module.mem_support_iff_of_finite.mpr hIq)
    have hm := Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (show RingHom.ker (Ideal.Quotient.mk I) ≤ q.asIdeal by simpa using hIq)
    simpa only [q, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] using hm
  let : Ring.KrullDimLE 0 Q := hdim
  let : IsArtinianRing Q := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let ht := Module.isTorsionBySet_annihilator R M
  let : Module Q M := ht.module
  let : IsNoetherian Q M :=
    (ht.semilinearMap.isNoetherian_iff_of_bijective Function.bijective_id).mp inferInstance
  have ha : IsArtinian R M :=
    (ht.semilinearMap.isArtinian_iff_of_bijective Function.bijective_id).mpr inferInstance
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, ha⟩

end Module

namespace Module
universe u v
variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- Finite-length modules are supported only at maximal primes. -/
theorem isMaximal_of_mem_support_of_length_ne_top
    (hM : Module.length A M ≠ ⊤) (p : PrimeSpectrum A)
    (hp : p ∈ Module.support A M) : p.asIdeal.IsMaximal := by
  have hf := Module.length_ne_top_iff.mp hM
  induction hf with
  | of_subsingleton =>
    simp only [Module.support_eq_empty, Set.mem_empty_iff_false] at hp
  | @of_simple_quotient N _ _ U _ hU ih =>
    rw [Module.support_of_exact (LinearMap.exact_subtype_mkQ U)
      (Submodule.subtype_injective U) (Submodule.mkQ_surjective U)] at hp
    rcases hp with hp | hp
    · exact ih (Module.length_ne_top_iff.mpr hU) hp
    · have hm := IsSimpleModule.annihilator_isMaximal (R := A) (M := N ⧸ U)
      exact hm.eq_of_le p.isPrime.ne_top
        (Module.annihilator_le_of_mem_support hp) ▸ hm

/-- The support criterion for finite length, proved from an actual finite
prime filtration. The ring is Noetherian and the module is finitely generated. -/
theorem length_ne_top_of_support_isMaximal [IsNoetherianRing A] [Module.Finite A M]
    (h : ∀ p : PrimeSpectrum A, p ∈ Module.support A M → p.asIdeal.IsMaximal) :
    Module.length A M ≠ ⊤ := by
  classical
  obtain ⟨D⟩ := nonempty_primeFiltration (A := A) M
  have he := D.length_eq_add_sum
  have hlen : ∀ p ∈ D.primes, Module.length A (A ⧸ p) = 1 := by
    intro p hp
    let : p.IsMaximal := h ⟨p, D.primes_isPrime p hp⟩ (D.prime_mem_support p hp)
    have : IsSimpleModule A (A ⧸ p) := by
      exact isSimpleModule_iff_quot_maximal.mpr ⟨p, inferInstance, ⟨LinearEquiv.refl A _⟩⟩
    exact Module.length_eq_one A (A ⧸ p)
  have hsum : (D.primes.map fun p => Module.length A (A ⧸ p)).sum ≠ ⊤ := by
    have aux : ∀ ps : List (Ideal A),
        (∀ p ∈ ps, Module.length A (A ⧸ p) = 1) →
        (ps.map fun p => Module.length A (A ⧸ p)).sum ≠ ⊤ := by
      intro ps
      induction ps with
      | nil => intro _; simp
      | cons p ps ih =>
        intro hh
        have hp := hh p (by simp)
        have hs := ih (fun q hq => hh q (List.mem_cons_of_mem p hq))
        simpa only [List.map_cons, List.sum_cons, hp, ne_eq, ENat.add_eq_top,
          ENat.one_ne_top, false_or] using hs
    exact aux D.primes hlen
  rw [he, Module.length_bot, zero_add]
  exact hsum

end Module
