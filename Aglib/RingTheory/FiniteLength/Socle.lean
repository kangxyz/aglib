/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Nonzero socle elements over a local ring

The socle obstruction used in finite-length arguments needs only the Artinian
condition: a nonzero Artinian module has a simple submodule, and the unique
maximal ideal annihilates that submodule.
-/

@[expose] public section

namespace IsArtinian

/-- The residue field embeds into every nonzero Artinian module over a
commutative local ring. -/
theorem exists_injective_residueField (R : Type*) (M : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [IsArtinian R M] [Nontrivial M] :
    ∃ f : IsLocalRing.ResidueField R →ₗ[R] M, Function.Injective f := by
  obtain ⟨N, hN⟩ := IsAtomic.exists_atom (Submodule R M)
  have hsimple : IsSimpleModule R N := isSimpleModule_iff_isAtom.mpr hN
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨N.subtype.comp e.symm.toLinearMap, N.subtype_injective.comp e.symm.injective⟩

/-- A nonzero Artinian module over a commutative local ring has a nonzero
vector annihilated by every element of the maximal ideal. -/
theorem exists_ne_zero_annihilated_maximalIdeal (R : Type*) (M : Type*) [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [IsArtinian R M] [Nontrivial M] :
    ∃ m : M, m ≠ 0 ∧ ∀ r ∈ IsLocalRing.maximalIdeal R, r • m = 0 := by
  obtain ⟨N, hN⟩ := IsAtomic.exists_atom (Submodule R M)
  have : IsSimpleModule R N := isSimpleModule_iff_isAtom.mpr hN
  have : Nontrivial N := IsSimpleModule.nontrivial R N
  obtain ⟨n, hn⟩ := exists_ne (0 : N)
  have hann : Module.annihilator R N = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal IsSimpleModule.annihilator_isMaximal
  refine ⟨n, fun h => hn (Subtype.ext h), fun r hr => ?_⟩
  have hz : r • n = 0 := Module.mem_annihilator.mp (hann.symm ▸ hr) n
  exact congrArg Subtype.val hz

end IsArtinian
