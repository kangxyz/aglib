/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite submodule approximation after localization

Finite submodules of a localized module lift to finitely generated submodules before
localization. The module, its localization and the ambient coefficient ring retain their
independent universes; no Noetherian hypothesis is required.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/FiniteApproximation.lean`.
SHA-256: `15b064e895d484e4c113df20099615f76fe6d8420248a1e551746d3c20a13c63`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
namespace IsLocalizedModule

/-- A finite localized module is already the localization of some finitely
generated submodule of the original, possibly infinitely generated, module. -/
theorem exists_fg_submodule_localized_eq_top
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (p : Submonoid R) (S : Type w) [CommRing S] [Algebra R S] [IsLocalization p S]
    {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) [IsLocalizedModule p f] [Module.Finite S N] :
    ∃ L : Submodule R M, L.FG ∧ L.localized' S p f = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := N)
  choose a ha using fun n : (s : Set N) => IsLocalizedModule.mk'_surjective p f n.1
  dsimp only [Function.uncurry] at ha
  let t : Finset M := Finset.univ.image (fun n : (s : Set N) => (a n).1)
  let L : Submodule R M := Submodule.span R (t : Set M)
  refine ⟨L, Submodule.fg_span t.finite_toSet, ?_⟩
  apply top_unique
  rw [← hs]
  apply Submodule.span_le.mpr
  intro n hn
  exact ⟨(a ⟨n, hn⟩).1, Submodule.subset_span (Finset.mem_image.mpr
    ⟨⟨n, hn⟩, Finset.mem_univ _, rfl⟩), (a ⟨n, hn⟩).2, ha ⟨n, hn⟩⟩

/-- Every finitely generated submodule of a localized module lifts to a
finitely generated submodule of the original module, with exactly the given
localization. The ambient localized module need not itself be finite. -/
theorem exists_fg_submodule_localized_eq
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (p : Submonoid R) (S : Type w) [CommRing S] [Algebra R S] [IsLocalization p S]
    {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) [IsLocalizedModule p f]
    (A : Submodule S N) (hA : A.FG) :
    ∃ L : Submodule R M, L.FG ∧ L.localized' S p f = A := by
  classical
  obtain ⟨s, hs⟩ := hA
  choose a ha using fun n : (s : Set N) => IsLocalizedModule.mk'_surjective p f n.1
  dsimp only [Function.uncurry] at ha
  let t : Finset M := Finset.univ.image (fun n : (s : Set N) => (a n).1)
  let L : Submodule R M := Submodule.span R (t : Set M)
  refine ⟨L, Submodule.fg_span t.finite_toSet, le_antisymm ?_ ?_⟩
  · rw [show L = Submodule.span R (t : Set M) from rfl, Submodule.localized'_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hm
    rw [← IsLocalizedModule.mk'_cancel' f (a n).1 (a n).2, ha n]
    exact A.smul_of_tower_mem _ (by rw [← hs]; exact Submodule.subset_span n.2)
  · rw [← hs]
    apply Submodule.span_le.mpr
    intro n hn
    exact ⟨(a ⟨n, hn⟩).1, Submodule.subset_span (Finset.mem_image.mpr
      ⟨⟨n, hn⟩, Finset.mem_univ _, rfl⟩), (a ⟨n, hn⟩).2, ha ⟨n, hn⟩⟩

/-- One finite submodule captures finitely many finite localized modules.
This is the finite-patch approximation required for a compact open cover. -/
theorem exists_fg_submodule_localized_eq_top_finite
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {ι : Type w} [Finite ι] (p : ι → Submonoid R)
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, IsLocalization (p i) (S i)]
    (N : ι → Type v) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module (S i) (N i)] [∀ i, IsScalarTower R (S i) (N i)]
    (f : ∀ i, M →ₗ[R] N i) [∀ i, IsLocalizedModule (p i) (f i)]
    [∀ i, Module.Finite (S i) (N i)] :
    ∃ L : Submodule R M, L.FG ∧ ∀ i, L.localized' (S i) (p i) (f i) = ⊤ := by
  classical
  choose L hL htop using fun i => exists_fg_submodule_localized_eq_top (p i) (S i) (f i)
  refine ⟨⨆ i, L i, Submodule.fg_iSup L hL, fun i => ?_⟩
  apply top_unique
  rw [← htop i]
  exact (Submodule.localized'gi (S i) (p i) (f i)).gc.monotone_l (le_iSup L i)

end IsLocalizedModule
